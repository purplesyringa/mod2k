use core::time::Duration;
use mod2k::*;
use num_modular::{Reducer, Vanilla};
use std::collections::HashMap;

macro_rules! for_each_modulus {
    ($macro_name:tt) => {
        // `worst_shift = (d_order / 2) * k`. `/ 2` ensures that both `q % d_order` and
        // `(-q) % d_order` are large, so that the performance of negative shifts is also measured.
        // For `BigPrime64`, `u64::MAX / k < d_order`, so we use `i64::MAX` as the almost-largest
        // value.
        $macro_name!(BigPrime8, shr = true, worst_shift = 96);
        $macro_name!(BigPrime16, shr = true, worst_shift = 4672);
        $macro_name!(BigPrime32, shr = true, worst_shift = 34359738304);
        $macro_name!(BigPrime64, shr = true, worst_shift = 9223372036854775807);
        // `worst_shift = k` guarantees both `n` and `-n` are outside `0..k`.
        $macro_name!(Prime7, shr = true, worst_shift = 7);
        $macro_name!(Prime13, shr = true, worst_shift = 13);
        $macro_name!(Prime31, shr = true, worst_shift = 31);
        $macro_name!(Prime61, shr = true, worst_shift = 61);
        $macro_name!(Fast8, shr = true, worst_shift = branchless);
        $macro_name!(Fast16, shr = true, worst_shift = branchless);
        $macro_name!(Fast32, shr = true, worst_shift = branchless);
        $macro_name!(Fast64, shr = true, worst_shift = branchless);
        $macro_name!(Power8, shr = false, worst_shift = branchless);
        $macro_name!(Power16, shr = false, worst_shift = branchless);
        $macro_name!(Power32, shr = false, worst_shift = branchless);
        $macro_name!(Power64, shr = false, worst_shift = branchless);
    };
}

trait FromSeed: Sized + Copy {
    fn from_seed(seed: u64) -> Self;
}

trait BlackBox {
    fn black_box(self) -> Self;
}

impl FromSeed for () {
    fn from_seed(_seed: u64) {}
}

impl BlackBox for () {
    fn black_box(self) {}
}

macro_rules! define_for_uint {
    ($ty:tt, $reg_class:tt) => {
        impl FromSeed for $ty {
            fn from_seed(seed: u64) -> Self {
                seed as Self
            }
        }

        impl BlackBox for $ty {
            fn black_box(mut self) -> Self {
                // Slower than intended on x86-64 for bytes due to [1].
                // [1]: https://github.com/llvm/llvm-project/issues/172172
                #[allow(asm_sub_register, reason = "codegen")]
                unsafe {
                    core::arch::asm!(
                        "/* {0} */",
                        inout($reg_class) self,
                        options(nomem, preserves_flags, nostack), // deliberately impure
                    );
                }
                self
            }
        }
    };
}
#[cfg(target_arch = "x86_64")]
define_for_uint!(u8, reg_byte);
#[cfg(not(target_arch = "x86_64"))]
define_for_uint!(u8, reg);
define_for_uint!(u16, reg);
define_for_uint!(u32, reg);
define_for_uint!(u64, reg);

fn map_to_mod<T: Mod<Native: Into<u64> + core::ops::Shr<u32, Output = T::Native>>>(
    x: T::Native,
) -> T {
    let bitness = size_of::<T::Native>() as u32 * 8;
    let m = T::MODULUS.into();
    let shift = if m == 0 { 0 } else { bitness - m.ilog2() };
    // SAFETY: Shifting guarantees `x >> shift` is less than the modulus.
    unsafe { T::new_unchecked(x >> shift) }
}

macro_rules! define_for_mod {
    ($ty:tt $($rest:tt)*) => {
        impl FromSeed for $ty {
            fn from_seed(seed: u64) -> Self {
                map_to_mod(seed as <Self as Mod>::Native)
            }
        }

        impl BlackBox for $ty {
            fn black_box(self) -> Self {
                // SAFETY: Matches the return value of `to_raw`.
                unsafe { Self::new_unchecked(self.to_raw().black_box()) }
            }
        }
    };
}
for_each_modulus!(define_for_mod);

impl<T: FromSeed, U: FromSeed> FromSeed for (T, U) {
    fn from_seed(seed: u64) -> Self {
        (T::from_seed(seed), U::from_seed(seed))
    }
}

impl<T: BlackBox, U: BlackBox> BlackBox for (T, U) {
    fn black_box(self) -> Self {
        (self.0.black_box(), self.1.black_box())
    }
}

impl BlackBox for bool {
    #[allow(clippy::transmute_int_to_bool, reason = "must be zero-cost")]
    fn black_box(self) -> Self {
        // SAFETY: noop
        unsafe { core::mem::transmute((self as u8).black_box()) }
    }
}

impl<T: BlackBox> BlackBox for Option<T> {
    fn black_box(self) -> Self {
        self.map(T::black_box)
    }
}

fn serialize() {
    #[cfg(target_arch = "x86")]
    unsafe {
        core::arch::x86::_mm_lfence();
    }
    #[cfg(target_arch = "x86_64")]
    unsafe {
        core::arch::x86_64::_mm_lfence();
    }
    // TODO: handle other architectures
}

#[inline(never)] // reduce register pressure/make codegen more consistent
fn measure(mut f: impl FnMut()) -> f64 {
    let mut n_runs = 100000;
    let mut elapsed = Duration::default();
    while elapsed < Duration::from_millis(20) {
        serialize();
        let start = fastant::Instant::now();
        for _ in 0..n_runs {
            f();
        }
        serialize();
        elapsed = start.elapsed();
        n_runs *= 2;
    }
    elapsed.as_nanos() as f64 / n_runs as f64
}

struct Measurement {
    throughput_bound: Option<f64>,
    latency_bound: Option<f64>,
}

fn bencht_with_input<T: FromSeed + BlackBox, U: BlackBox>(
    x: T,
    mut f: impl FnMut(T) -> U,
) -> Measurement {
    Measurement {
        throughput_bound: {
            let f = &mut f;
            Some(measure(move || {
                f(x.black_box()).black_box();
            }))
        },
        latency_bound: None,
    }
}

fn bencht<T: FromSeed + BlackBox, U: BlackBox>(f: impl FnMut(T) -> U) -> Measurement {
    bencht_with_input(T::from_seed(0), f)
}

fn benchtl_with_input<T: FromSeed + BlackBox>(mut x: T, mut f: impl FnMut(T) -> T) -> Measurement {
    Measurement {
        throughput_bound: {
            let f = &mut f;
            Some(measure(move || {
                f(x.black_box()).black_box();
            }))
        },
        latency_bound: {
            let f = &mut f;
            Some(measure(move || x = f(x.black_box())))
        },
    }
}

fn benchtl<T: FromSeed + BlackBox>(f: impl FnMut(T) -> T) -> Measurement {
    benchtl_with_input(T::from_seed(0), f)
}

fn main() {
    let mut results: HashMap<&str, HashMap<&str, Measurement>> = HashMap::new();
    let mut bench_order: Vec<&str> = Vec::new();

    macro_rules! if_eq {
        (if branchless = branchless $then:block else $else:block) => {
            $then
        };
        (if $x:tt = branchless $then:block else $else:block) => {
            $else
        };
    }

    println!("Benchmarking... this should take about a minute, please wait for the completion");

    let mut add = |ty_name: &'static str, bench_name: &'static str, measurement: Measurement| {
        if !results.contains_key(bench_name) {
            bench_order.push(bench_name);
        }
        results
            .entry(bench_name)
            .or_default()
            .insert(ty_name, measurement);
    };

    macro_rules! bench_modulus {
        ($ty:tt, shr = $shr:tt, worst_shift = $worst_shift:tt) => {{
            let mut add = |bench_name, measurement| add(stringify!($ty), bench_name, measurement);

            // Branchless functions that take and return distinct types -- can reasonably only
            // measure throughput, since converting types would affect latency.
            add("new", bencht(|x| $ty::new(x)));
            add("remainder", bencht(|x: $ty| x.remainder()));
            add("is 1", bencht(|x: $ty| x.is::<1>()));
            add("is 100", bencht(|x: $ty| x.is::<100>()));
            add("is_zero", bencht(|x: $ty| x.is_zero()));
            add("eq", bencht(|(x, y): ($ty, $ty)| x == y));

            // Can be adjusted to take and return the same type -- measure latency and throughput.
            // Use `black_box` to avoid exposing that the two arguments are equal.
            add("add", benchtl(|x: $ty| x + x.black_box()));
            add("sub", benchtl(|x: $ty| x - x.black_box()));
            add("mul", benchtl(|x: $ty| x * x.black_box()));
            add("negate", benchtl(|x: $ty| -x));
            add(
                "shl limited",
                benchtl(|x: $ty| {
                    let n = 5u64.black_box();
                    unsafe {
                        core::hint::assert_unchecked(n <= 5);
                    }
                    x << n
                }),
            );
            #[cfg($shr)]
            {
                add(
                    "shr limited",
                    benchtl(|x: $ty| {
                        let n = 5u64.black_box();
                        unsafe {
                            core::hint::assert_unchecked(n <= 5);
                        }
                        x >> n
                    }),
                );
            }

            let n: u64;
            if_eq! {
                if $worst_shift = branchless {
                    n = u64::MAX;
                } else {
                    n = $worst_shift;
                }
            }
            add("shl", benchtl(|x: $ty| x << n.black_box()));
            #[cfg($shr)]
            {
                add(
                    "shl negative",
                    benchtl(|x: $ty| x << n.wrapping_neg().black_box() as i64),
                );
                add("shr", benchtl(|x: $ty| x >> n.black_box()));
                add(
                    "shr negative",
                    benchtl(|x: $ty| x >> n.wrapping_neg().black_box() as i64),
                );
            }

            // `PowerK` optimizes `pow` for even `x`, so force an odd input.
            let n = u64::MAX.black_box();
            add("pow", benchtl_with_input($ty::new(1), |x: $ty| x.pow(n)));

            // Ironically, 1 is the worst input for binary GCD. `1^-1 = 1`, so this repeats
            // indefinitely.
            add(
                "inverse worst",
                benchtl_with_input($ty::ONE.black_box(), |x| x.inverse().unwrap()),
            );
            add(
                "is_invertible worst",
                bencht_with_input($ty::ONE.black_box(), |x| x.is_invertible()),
            );

            let mut rng = fastrand::Rng::new();
            add(
                "inverse random",
                bencht(|()| $ty::from_seed(rng.u64(..)).inverse()),
            );
            add(
                "is_invertible random",
                bencht(|()| $ty::from_seed(rng.u64(..)).is_invertible()),
            );
        }};
    }
    // for_each_modulus!(bench_modulus);

    macro_rules! bench_num_modular {
        ($ty_name:literal, $modulus:expr) => {{
            let mut add = |bench_name, measurement| add($ty_name, bench_name, measurement);
            let reducer = Vanilla::new(&$modulus);
            add("new", bencht(|x| reducer.transform(x)));
            add("add", benchtl(|x| reducer.add(&x, &x.black_box())));
            add("sub", benchtl(|x| reducer.sub(&x, &x.black_box())));
            add("mul", benchtl(|x| reducer.mul(&x, &x.black_box())));
            add("negate", benchtl(|x| reducer.neg(x)));
            let mut rng = fastrand::Rng::new();
            add(
                "inverse random",
                bencht(|()| reducer.inv(reducer.transform(rng.u64(..) as _))),
            );
        }};
    }
    bench_num_modular!("Vanilla8", (1u8 << 7) - 1);
    bench_num_modular!("Vanilla16", (1u16 << 13) - 1);
    bench_num_modular!("Vanilla32", (1u32 << 31) - 1);
    bench_num_modular!("Vanilla64", (1u64 << 61) - 1);

    for bench_name in bench_order {
        println!("{bench_name}:");
        let bench_results = &results[bench_name];
        macro_rules! print_modulus {
            ($ty_name:tt $($rest:tt)*) => {
                print!("\t{}: ", stringify!($ty_name));
                match bench_results.get(stringify!($ty_name)) {
                    Some(measurement) => {
                        match measurement.throughput_bound {
                            Some(n) => print!("{n:.2}ns"),
                            None => print!("--"),
                        }
                        print!(" / ");
                        match measurement.latency_bound {
                            Some(n) => print!("{n:.2}ns"),
                            None => print!("--"),
                        }
                        println!();
                    }
                    None => println!("n/a"),
                }
            };
        }
        for_each_modulus!(print_modulus);
        print_modulus!(Vanilla8);
        print_modulus!(Vanilla16);
        print_modulus!(Vanilla32);
        print_modulus!(Vanilla64);
    }
}
