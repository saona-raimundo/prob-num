# TODO

- Into
  - [rand_distr](https://docs.rs/rand_distr/0.4.1/rand_distr/index.html)::[WeightedIndex](https://docs.rs/rand_distr/0.4.1/rand_distr/struct.WeightedIndex.html#)
- TryInto
  - [rand_distr](https://docs.rs/rand_distr/0.4.1/rand_distr/index.html)::[weighted_alias](https://docs.rs/rand_distr/0.4.1/rand_distr/weighted_alias/index.html)::[WeightedAliasIndex](https://docs.rs/rand_distr/0.4.1/rand_distr/weighted_alias/struct.WeightedAliasIndex.html#)
- macro definitions
  - dens!
    Similar to vec!

# Probability

## Trait implementation (derivation)

- [ ] Check that we have as many implementations as 
  - [x] Closed01
  - [ ] Complex
  - [ ] Ratio

### Num_traits

- [num_traits](https://docs.rs/num-traits/0.2.14/num_traits/index.html)::[int](https://docs.rs/num-traits/0.2.14/num_traits/int/index.html)::[PrimInt](https://docs.rs/num-traits/0.2.14/num_traits/int/trait.PrimInt.html)
- [num_traits](https://docs.rs/num-traits/0.2.14/num_traits/index.html)::[float](https://docs.rs/num-traits/0.2.14/num_traits/float/index.html)::[Float](https://docs.rs/num-traits/0.2.14/num_traits/float/trait.Float.html)
- pub use ops::wrapping::WrappingAdd;
- pub use ops::wrapping::WrappingMul;
- pub use ops::wrapping::WrappingSub;
- pub use pow::Pow;
  - Check all implementations of Pow in num_complex

# Density

# Weights

# Distribution

