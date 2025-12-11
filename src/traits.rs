/// A common interface for modular arithmetic.
///
/// This trait is implemented by all types in this crate.
pub trait Mod: Sized {
    /// The underlying native type.
    type Native;

    /// A constant `0` value.
    const ZERO: Self;

    /// A constant `1` value.
    const ONE: Self;

    /// Create a value corresponding to `x mod m`.
    fn new(x: Self::Native) -> Self;

    /// Create a value corresponding to `x`, assuming `x < m`.
    ///
    /// This function is most useful for prime moduli, for which `from_remainder_unchecked` is
    /// faster than [`new`](Self::new). For fast and power-of-two moduli, the performance is
    /// equivalent.
    ///
    /// # Safety
    ///
    /// This function is only valid to call if `x` is less than the modulus.
    unsafe fn from_remainder_unchecked(x: Self::Native) -> Self;

    /// Get the normalized residue `x mod m`.
    fn remainder(self) -> Self::Native;

    /// Get the internal optimized representation of the number.
    ///
    /// This returns some value equivalent to `x` modulo `m`, but not necessarily `x mod m` itself.
    /// This is more efficient than [`remainder`](Self::remainder) for prime moduli. Passing this
    /// value back to [`new`](Self::new) is guaranteed to produce the same value as `self`.
    fn to_raw(self) -> Self::Native;

    /// Compare for equality with a constant.
    ///
    /// For fast moduli, this is more efficient than `x == FastK::new(C)`. `C` must be a valid
    /// reminder, i.e. `C < m`.
    ///
    /// `C` is typed `u64` instead of [`Native`](Self::Native) due to Rust having issues with
    /// associated types in `const`.
    fn is<const C: u64>(self) -> bool;

    /// Compare for equality with zero.
    ///
    /// This is equivalent to `is::<0>()`.
    fn is_zero(&self) -> bool;

    /// Compute `x^n mod m`.
    ///
    /// The current implementation uses iterative binary exponentiation, combining it with [the
    /// Carmichael function][1] to reduce exponents. It works in `O(log n)`.
    ///
    /// [1]: https://en.wikipedia.org/wiki/Carmichael_function
    fn pow(self, n: u64) -> Self;

    /// Check if the value is invertible, i.e. if `x` is coprime with `m`.
    ///
    /// For fast and prime moduli, the current implementation uses the binary Euclidean algorithm,
    /// which works in `O(k)`. For power-of-two moduli, it checks `x` if odd.
    fn is_invertible(&self) -> bool;

    /// Compute multiplicative inverse.
    ///
    /// Returns `None` if `x` is not coprime with `m`.
    ///
    /// For fast and prime moduli, the current implementation uses the iterative binary extended
    /// Euclidean algorithm, which works in `O(k)`. For power-of-two moduli, it uses [Hensel
    /// lifting][hensel], which works in `O(log k)`.
    ///
    /// [hensel]: https://en.wikipedia.org/wiki/Modular_multiplicative_inverse#Inverses_modulo_prime_powers_(including_powers_of_2)
    fn inverse(self) -> Option<Self>;
}
