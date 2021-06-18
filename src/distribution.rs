use num_traits::identities::{One, Zero};

/// [Cummulative distribution], ie increasing numbers in [0, 1].
///
/// [Cummulative distribution]: https://en.wikipedia.org/wiki/Cumulative_distribution_function
#[derive(Debug)]
pub struct Distribution<T, const N: usize>([T; N])
where
    T: PartialOrd + Zero + One;
