use crate::P;
use core::{convert::TryFrom, fmt::Debug, iter::Sum, ops::Index};
use num_traits::identities::{One, Zero};

mod error;
mod iter;
mod serde_impl;

pub use error::{Bound, TotalMass};
pub use iter::IntoIter;

/// Shorthand for `Density`.
pub type D<T, const N: usize> = Density<T, N>;

/// [Probability mass function] or density, ie a collection of numbers in [0, 1] that sum up to 1.
///
/// # Remarks
///
/// The elements sum exactly one. Therefore, using floating point is rather limited.
/// For an approximate version, see `Weights`.
///
/// [Probability mass function]: https://en.wikipedia.org/wiki/Probability_mass_function
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Density<T, const N: usize>(pub(crate) [P<T>; N])
where
    T: PartialOrd + Zero + One;

impl<T, const N: usize> Density<T, N>
where
    T: PartialOrd + Zero + One,
{
    /// Returns the value stored.
    #[inline]
    pub fn get(&self) -> &[P<T>; N] {
        &self.0
    }

    /// Returns the value stored.
    #[inline]
    pub fn into_inner(self) -> [P<T>; N] {
        self.0
    }
}

impl<T, const N: usize> Density<T, N>
where
    T: PartialOrd + Zero + One + Copy,
{
    /// Constructs a new `Density<T, N>`.
    ///
    /// # Remarks
    ///
    /// There is no checking of the input.
    #[inline]
    pub fn new_unchecked(probabilities: [T; N]) -> Self {
        let mut vector = [P::new_unchecked(T::zero()); N];
        for (i, p) in probabilities.iter().enumerate() {
            vector[i] = P::new_unchecked(*p);
        }
        Density(vector)
    }
}

impl<T, const N: usize> Density<T, N>
where
    T: PartialOrd + Zero + One + Copy + Debug + Sum,
{
    /// Constructs a new `Density<T, N>`.
    ///
    /// # Panics
    ///
    /// If the input is not in the interval [0, 1].
    #[inline]
    pub fn new(probabilities: [T; N]) -> Self {
        assert!(N > 0);
        let sum: T = probabilities.iter().cloned().sum();
        assert_eq!(sum, T::one());
        let mut vector = [P::new_unchecked(T::zero()); N];
        for (i, p) in probabilities.iter().enumerate() {
            vector[i] = P::new(*p);
        }

        Density(vector)
    }

    /// Constructs a new `Density<T, N>`.
    ///
    /// # Panics
    ///
    /// In debug mode, if the input is not in the interval [0, 1].
    #[inline]
    pub fn new_debug_checked(probabilities: [T; N]) -> Self {
        debug_assert!(N > 0);
        let sum: T = probabilities.iter().cloned().sum();
        debug_assert_eq!(sum, T::one());
        let mut vector = [P::new_unchecked(T::zero()); N];
        for (i, p) in probabilities.iter().enumerate() {
            vector[i] = P::new_debug_checked(*p);
        }
        Density(vector)
    }
}

impl<T: 'static, const N: usize> TryFrom<[T; N]> for Density<T, N>
where
    T: PartialOrd + Zero + One + Copy + Debug + Sum<T>,
{
    type Error = Bound<T>;
    fn try_from(probabilities: [T; N]) -> Result<Self, Self::Error> {
        if N == 0 {
            return Err(Bound::Empty);
        }
        let sum = probabilities.iter().cloned().sum();
        if sum > T::one() {
            Err(TotalMass::TooMuch(sum))?;
        }
        if sum < T::one() {
            Err(TotalMass::TooLittle(sum))?;
        }
        let mut vector = [P::new_unchecked(T::zero()); N];
        for (i, p) in probabilities.iter().enumerate() {
            vector[i] = P::try_new(*p)?;
        }

        Ok(Density(vector))
    }
}

impl<T, const N: usize> Density<T, N>
where
    T: PartialOrd + Zero + One + Copy + Debug + Sum<T>,
{
    /// Performs the conversion.
    #[inline]
    pub fn try_new(probabilities: [T; N]) -> Result<Self, Bound<T>> {
        if N == 0 {
            return Err(Bound::Empty);
        }
        let sum = probabilities.iter().cloned().sum();
        if sum > T::one() {
            Err(TotalMass::TooMuch(sum))?;
        }
        if sum < T::one() {
            Err(TotalMass::TooLittle(sum))?;
        }
        let mut vector = [P::new_unchecked(T::zero()); N];
        for (i, p) in probabilities.iter().enumerate() {
            vector[i] = P::try_new(*p)?;
        }

        Ok(Density(vector))
    }
}

impl<T, const N: usize> AsRef<[P<T>]> for Density<T, N>
where
    T: PartialOrd + Zero + One + Copy,
{
    #[inline]
    fn as_ref(&self) -> &[P<T>] {
        self.get().as_ref()
    }
}

impl<T, const N: usize> Default for Density<T, N>
where
    T: PartialOrd + Zero + One + Copy,
{
    /// Returns the “default value” of a density that has full mass in the first element.
    ///
    /// # Panics
    ///
    /// If `N` is zero.
    fn default() -> Self {
        assert!(N > 0);
        let mut probabilities = [T::zero(); N];
        probabilities[0] = T::one();
        Density::new_unchecked(probabilities)
    }
}

impl<T, const N: usize> Index<usize> for Density<T, N>
where
    T: PartialOrd + Zero + One,
{
    type Output = P<T>;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.get()[index]
    }
}

impl<T, const N: usize> IntoIterator for Density<T, N>
where
    T: PartialOrd + Zero + One + Clone,
{
    type Item = P<T>;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<T: 'static, const N: usize> TryFrom<[P<T>; N]> for Density<T, N>
where
    T: PartialOrd + Zero + One + Debug + Clone + Sum,
{
    type Error = error::Bound<T>;
    fn try_from(probabilities: [P<T>; N]) -> Result<Self, <Self as TryFrom<[P<T>; N]>>::Error> {
        if N == 0 {
            return Err(Bound::Empty);
        }
        let sum = probabilities.iter().cloned().map(|p| p.into_inner()).sum();
        if sum > T::one() {
            Err(TotalMass::TooMuch(sum))?;
        } else if sum < T::one() {
            Err(TotalMass::TooLittle(sum))?;
        }

        Ok(Density(probabilities))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use test_case::test_case;

    #[test]
    fn default() {
        let d = Density::default();
        assert_eq!(d, Density::new_unchecked([1, 0, 0]));
    }

    #[test_case([0.5, 0.5], "(((0.5),(0.5)))"; "half half")]
    #[test_case([0.5, 0.1, 0.4], "(((0.5),(0.1),(0.4)))"; "three elements")]
    #[test_case([0.1; 10], "(((0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1)))"; "ten elements")]
    fn deserialize<'de, T, const N: usize>(probabilities: [T; N], s: &'de str)
    where
        T: PartialOrd + Zero + One + Copy + Debug + serde::Deserialize<'de>,
    {
        let d: Density<T, N> = Density::new_unchecked(probabilities);
        let d2 = ron::de::from_str(s).unwrap();
        println!("{:?}", s);
        assert_eq!(d, d2);
    }

    #[test]
    fn index() {
        let d = Density::new([0.2, 0.8]);
        assert_eq!(P::new(0.2), d[0]);
        assert_eq!(P::new(0.8), d[1]);
    }

    #[test_case([1./9., 8./9.]; "2 elements")]
    #[test_case([0.4, 0.4, 0.2]; "3 elements")]
    #[test_case([1./3.; 3]; "thirds")]
    #[test_case([1./5.; 5]; "5 elements")]
    #[test_case([1./6.; 6] => panics; "6 elements")]
    #[test_case([0.1_f64; 10] => panics; "10 elements")]
    fn new<T, const N: usize>(probabilities: [T; N])
    where
        T: PartialOrd + Zero + One + Copy + Debug + Sum,
    {
        D::new(probabilities);
    }

    #[test_case([0.5, 0.5], "(((0.5),(0.5)))"; "half half")]
    #[test_case([0.5, 0.1, 0.4], "(((0.5),(0.1),(0.4)))"; "three elements")]
    #[test_case([0.1; 10], "(((0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1),(0.1)))"; "ten elements")]
    fn serialize<T, const N: usize>(probabilities: [T; N], expected: &str)
    where
        T: PartialOrd + Zero + One + Copy + Debug + serde::Serialize,
    {
        let d = Density::new_unchecked(probabilities);
        let s = ron::ser::to_string(&d).unwrap();
        assert_eq!(s, expected);
    }

    #[test_case([0, -1, 1, 1] => Err(Bound::Element { source: crate::probability::Bound::Lower(-1) }) ; "wrong single probability")]
    #[test_case([0, 1, 1] => Err(Bound::TotalMass { source: TotalMass::TooMuch(2) }) ; "wrong total mass probability")]
    #[test_case([0.5, 0.5] => Ok(Density::new_unchecked([0.5, 0.5])) ; "half half")]
    fn try_new<T, const N: usize>(probabilities: [T; N]) -> Result<Density<T, N>, Bound<T>>
    where
        T: PartialOrd + Zero + One + Copy + Debug + Sum<T> + 'static,
    {
        Density::try_new(probabilities)
    }
}
