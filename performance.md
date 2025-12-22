This benchmark compares types in the `mod2k` crate to each other.

---

It does *not* compare `mod2k` to other crates, because this is impossible to do diligently. The closest crate would be [num-modular](https://docs.rs/num-modular/), but it'd be an incredibly apples-to-oranges comparison:

- `num-modular` does not implement some feature of `mod2k`, like shifts.
- `num-modular` does not implement some worst-case protection, like in `pow`. Showing just the worst case would be dishonest because few people will trigger it, but it's not clear what the average case is.
- `num-modular` emits *a lot* of branching code. Even `-` branches. At the scale in question, it's impossible to generate random data to demonstrate branch misprediction fast enough to avoid skewing the results.

Basically the only usable piece of information I could extract is that `num-modular` spends 0.50 ns on adding numbers. That's worse than `mod2k` in all configurations, and about 2x worse than the `prime` configuration. It is also slow at `new`/`convert`, using the `div` instruction even with a fixed modulus for whatever reason, and at inverse calculation, spending 4x more time than `mod2k`. Based on [rigid scientific extrapolation](https://xkcd.com/605/), I'd expect `mod2k` to be at least 2x faster than `num-modular` on average, and at least 1.5x faster than a moderately optimized textbook implementation, but this may vary wildly in practice.

---

This data is a rough approximation of multiple independent microbenchmarks. As always, prefer to measure performance of practical code: microbenchmarks don't paint the full picture, due to optimizer deficiencies if nothing else.

For cells with `/`, the first number measures throughput-bound code, and the second number measures latency-bound code. For cells without `/`, the sole measurement is throughput-bound. 64-bit moduli are sometimes consistently slower than smaller types, so they are shown separately when relevant.

|Time per op (ns)|`big_prime`|`prime`|`fast`|`power`|
|---|---|---|---|---|
|`new`|0.14|0.34|0.14|0.14|
|`remainder`|0.20|0.14|0.17|0.14|
|`is::<1>`|0.24|0.14|0.14|0.14|
|`is::<100>`|0.14|0.14|0.14|0.14|
|`is_zero`|0.24|0.14|0.18|0.14|
|`==`|0.39|0.18|0.27|0.18|
|`+`|0.40 / 0.88|0.27 / 0.53|0.18 / 0.29|0.14 / 0.14|
|`-`|0.40 / 0.80|0.24 / 0.42|0.20 / 0.28|0.14 / 0.14|
|`-` (unary)|0.27 / 0.56|0.24 / 0.42|0.14 / 0.14|0.14 / 0.14|
|`*`|0.40 / 1.40<br>0.56 / 2.09 (64-bit)|0.44 / 1.40|0.26 / 0.81|0.14 / 0.42|
|`<<` (small amount)|0.50 / 1.60<br>0.99 / 2.24 (64-bit)|0.43 / 0.71<br>0.63 / 1.20 (64-bit)|0.26 / 0.26|0.26 / 0.26|
|`>>` (small amount)|1.20 / 1.64<br>2.15 / 2.41 (64-bit)|0.43 / 0.57<br>0.57 / 1.20 (64-bit)|0.26 / 0.26|n/a|
|`<<` (max amount)|slow, scales linearly<br>worst-case 129/134 (64-bit)|0.83 / 0.90<br>1.10 / 1.21 (64-bit)|0.26 / 0.26|0.32 / 0.32|
|`>>` (max amount)|slow, scales linearly<br>worst-case 129/146 (64-bit)|0.83 / 0.90<br>1.10 / 1.21 (64-bit)|0.26 / 0.26|n/a|
|`<<` (max negative amount)|slow, scales linearly<br>worst-case 137/137 (64-bit)|1.05 / 1.11<br>1.33 / 1.46 (64-bit)|0.26 / 0.26|n/a|
|`>>` (max negative amount)|slow, scales linearly<br>worst-case 141/149 (64-bit)|1.05 / 1.11<br>1.33 / 1.46 (64-bit)|0.26 / 0.26|n/a|
|`is_invertible`|0.25|0.14|1.14<br>3.31 (64-bit)|0.14|

The performance of `pow` significantly depends on `n`. This table shows timings for the worst possible `n`:

|Time per op (ns)|`big_prime`|`prime`|`fast`|`power`|
|---|---|---|---|---|
|8-bit|15|13|5|3|
|16-bit|26|20|8|6|
|32-bit|53|44|13|12|
|64-bit|148|106|26|25|

The performance of `inverse` significantly depends on the input value. This table shows timings for a random input:

|Time per op (ns)|`big_prime`|`prime`|`fast`|`power`|
|---|---|---|---|---|
|8-bit|9|9|10|0.19 / 0.76|
|16-bit|17|15|18|0.38 / 1.80|
|32-bit|35|39|36|0.50 / 2.34|
|64-bit|69|68|55|0.75 / 2.73|
