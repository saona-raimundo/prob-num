# prob-num

Generic probability numerical representations for Rust

## Aim

To be as useful as [num](https://crates.io/crates/num) related structs, focused on probability related structs like single probabilities, densities and distributions.

## Main types

Probabilities and distributions

- `P<T>` represents a single probability
- `D<T, N>` represents a density

## Features

- Type agnostic
  Use any type `T` to construct probabilities `P<T>`or distributions `D<T, N>`. This includes:
  - floats
  - rationals
  - unums or posits
  - etc...
- Traits from `num-traits` derived, if `T` implements it.

## Similar crates

- [closed01](https://crates.io/crates/closed01)
  Floats restricted to the interval [0, 1].
- [nalgebra](https://docs.rs/nalgebra/0.27.1/nalgebra/index.html)::[base](https://docs.rs/nalgebra/0.27.1/nalgebra/base/index.html)::[Unit](https://docs.rs/nalgebra/0.27.1/nalgebra/base/struct.Unit.html#)
  Unit norm values.
- [num_complex](https://docs.rs/num-complex/0.4.0/num_complex/index.html)::[Complex](https://docs.rs/num-complex/0.4.0/num_complex/struct.Complex.html)
  Complex number, based on a generic type
- [num_rational](https://docs.rs/num-rational/0.4.0/num_rational/index.html)::[Ratio](https://docs.rs/num-rational/0.4.0/num_rational/struct.Ratio.html)
  Rational number, based on a generic type