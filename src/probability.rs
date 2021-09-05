use approx::{AbsDiffEq, RelativeEq, UlpsEq};
use core::{
    fmt::{Debug, Display},
    iter::Sum,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};
use num_traits::{
    cast::{AsPrimitive, FromPrimitive, NumCast, ToPrimitive},
    identities::{One, Zero},
    ops::{
        checked::{CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedSub},
        mul_add::{MulAdd, MulAddAssign},
        saturating::{SaturatingAdd, SaturatingMul, SaturatingSub},
    },
    sign::Unsigned,
    Bounded, Num,
};
use serde::{Deserialize, Serialize};

mod error;

pub use error::Bound;

/// Shorthand for `Probability`.
pub type P<T> = Probability<T>;

/// Wrapper over a probability value, ie a number in the range [0, 1] including both endpoints.
#[derive(
    Copy, Clone, Debug, Default, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize,
)]
pub struct Probability<T>(T)
where
    T: PartialOrd + Zero + One;

impl<T> P<T>
where
    T: PartialOrd + Zero + One,
{
    /// Constructs a new `P<T>`.
    ///
    /// # Panics
    ///
    /// If the input is not in the interval [0, 1].
    #[inline]
    pub fn new(p: T) -> Self {
        assert!(!(p < T::zero()) && !(p > T::one()));
        Probability(p)
    }

    /// Constructs a new `P<T>`.
    ///
    /// # Panics
    ///
    /// In debug mode, if the input is not in the interval [0, 1].
    #[inline]
    pub fn new_debug_checked(p: T) -> Self {
        debug_assert!(!(p < T::zero()) && !(p > T::one()));
        Probability(p)
    }

    /// Constructs a new `P<T>`.
    ///
    /// # Remarks
    ///
    /// There is no checking of the input.
    #[inline]
    pub fn new_unchecked(p: T) -> Self {
        Probability(p)
    }

    /// Returns the value stored.
    #[inline]
    pub fn get(&self) -> &T {
        &self.0
    }

    /// Returns the value stored.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.0
    }

    /// Returns the value stored.
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }

    /// Apply a function, creating a probability with potentially other type.
    ///
    /// # Panics
    ///
    /// If the resulting value is not in [0, 1].
    #[inline]
    pub fn map<U, F>(self, mut f: F) -> P<U>
    where
        F: FnMut(T) -> U,
        U: PartialOrd + Zero + One,
    {
        P::new(f(self.into_inner()))
    }

    /// Apply a function, creating a probability with potentially other type.
    ///
    /// # Panics
    ///
    /// In debug mode, if the resulting value is not in [0, 1].
    #[inline]
    pub fn map_debug_checked<U, F>(self, mut f: F) -> P<U>
    where
        F: FnMut(T) -> U,
        U: PartialOrd + Zero + One,
    {
        P::new_debug_checked(f(self.into_inner()))
    }

    /// Apply a function, creating a probability with potentially other type.
    #[inline]
    pub fn map_unchecked<U, F>(self, mut f: F) -> P<U>
    where
        F: FnMut(T) -> U,
        U: PartialOrd + Zero + One,
    {
        P::new_unchecked(f(self.into_inner()))
    }

    /// Apply a function transforming the underlying value.
    ///
    /// # Panics
    ///
    /// If the resulting value is not in [0, 1].
    #[inline]
    pub fn map_inplace<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T),
    {
        f(self.get_mut());
        assert!(!(self.get() < &T::zero()) && !(self.get() > &T::one()));
    }

    /// Apply a function, creating a probability with potentially other type.
    ///
    /// # Panics
    ///
    /// In debug mode, if the resulting value is not in [0, 1].
    #[inline]
    pub fn map_inplace_debug_checked<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T),
    {
        f(self.get_mut());
        debug_assert!(!(self.get() < &T::zero()) && !(self.get() > &T::one()));
    }

    /// Apply a function, creating a probability with potentially other type.
    #[inline]
    pub fn map_inplace_unchecked<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T),
    {
        f(self.get_mut());
    }
}

impl<T> P<T>
where
    T: PartialOrd + Zero + One + Debug,
{
    /// Performs the conversion.
    ///
    /// # Remarks
    ///
    /// It replaces the implementation of the trait `TryFrom`.
    #[inline]
    pub fn try_new(p: T) -> Result<Self, Bound<T>> {
        if p < T::zero() {
            Err(Bound::Lower(p))
        } else if p > T::one() {
            Err(Bound::Upper(p))
        } else {
            Ok(P::new_unchecked(p))
        }
    }
}

impl<T> P<T>
where
    T: PartialOrd + Zero + One + Sub<Output = T>,
{
    /// Returns the absolute distance between the two probabilities.
    #[inline]
    pub fn distance(self, other: Self) -> Self {
        if self > other {
            P::new_unchecked(self.into_inner() - other.into_inner())
        } else {
            P::new_unchecked(other.into_inner() - self.into_inner())
        }
    }
}

impl<T> P<T>
where
    T: PartialOrd + Zero + One + Sub<Output = T> + Clone,
{
    /// Returns the arithmetic average of two values.
    #[inline]
    pub fn average(self, other: Self) -> Self {
        if self > other {
            other.clone() + P::new_unchecked(self.into_inner() - other.into_inner())
        } else {
            self.clone() + P::new_unchecked(other.into_inner() - self.into_inner())
        }
    }
}

impl<T> AbsDiffEq for P<T>
where
    T: PartialOrd + Zero + One + AbsDiffEq,
{
    type Epsilon = <T as AbsDiffEq>::Epsilon;
    fn default_epsilon() -> Self::Epsilon {
        T::default_epsilon()
    }
    fn abs_diff_eq(&self, other: &Self, epsilon: Self::Epsilon) -> bool {
        self.get().abs_diff_eq(other.get(), epsilon)
    }
}

impl<T> Add for P<T>
where
    T: PartialOrd + Zero + One,
{
    type Output = Self;
    fn add(self, other: Self) -> Self {
        P::new(self.into_inner() + other.into_inner())
    }
}

impl<T> AddAssign for P<T>
where
    T: PartialOrd + Zero + One + AddAssign,
{
    fn add_assign(&mut self, other: Self) {
        self.0 += other.into_inner();
    }
}

impl<T, U> AsPrimitive<U> for P<T>
where
    T: PartialOrd + Zero + One + AsPrimitive<U>,
    U: 'static + Copy,
{
    fn as_(self) -> U {
        self.into_inner().as_()
    }
}

impl<T> BitAnd for P<T>
where
    T: PartialOrd + Zero + One + BitAnd<Output = T>,
{
    type Output = Self;
    fn bitand(self, other: Self) -> Self::Output {
        P::new(self.into_inner() & other.into_inner())
    }
}

impl<T> BitAndAssign for P<T>
where
    T: PartialOrd + Zero + One + BitAndAssign,
{
    fn bitand_assign(&mut self, other: Self) {
        self.0 &= other.into_inner()
    }
}

impl<T> Bounded for P<T>
where
    T: PartialOrd + Zero + One,
{
    fn min_value() -> Self {
        Self::zero()
    }
    fn max_value() -> Self {
        Self::one()
    }
}

impl<T> CheckedAdd for P<T>
where
    T: PartialOrd + Zero + One + CheckedAdd,
{
    fn checked_add(&self, other: &Self) -> Option<Self> {
        match self.get().checked_add(other.get()) {
            Some(q) => {
                if q > T::one() {
                    None
                } else {
                    Some(P::new_unchecked(q))
                }
            }
            None => None,
        }
    }
}

impl<T> CheckedDiv for P<T>
where
    T: PartialOrd + Zero + One + CheckedDiv,
{
    fn checked_div(&self, other: &Self) -> Option<Self> {
        match self.get().checked_div(other.get()) {
            Some(q) => {
                if q > T::one() {
                    None
                } else {
                    Some(P::new_unchecked(q))
                }
            }
            None => None,
        }
    }
}

impl<T> CheckedMul for P<T>
where
    T: PartialOrd + Zero + One + CheckedMul,
{
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        match self.get().checked_mul(other.get()) {
            Some(q) => Some(P::new_unchecked(q)),
            None => None,
        }
    }
}

impl<T> CheckedRem for P<T>
where
    T: PartialOrd + Zero + One + CheckedRem,
{
    fn checked_rem(&self, other: &Self) -> Option<Self> {
        match self.get().checked_rem(other.get()) {
            Some(q) => {
                if q > T::one() {
                    None
                } else {
                    Some(P::new_unchecked(q))
                }
            }
            None => None,
        }
    }
}

impl<T> CheckedSub for P<T>
where
    T: PartialOrd + Zero + One + CheckedSub,
{
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        match self.get().checked_sub(other.get()) {
            Some(q) => {
                if q < T::zero() {
                    None
                } else {
                    Some(P::new_unchecked(q))
                }
            }
            None => None,
        }
    }
}

impl<T> Display for P<T>
where
    T: PartialOrd + Zero + One + Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.get())
    }
}

impl<T> Div for P<T>
where
    T: PartialOrd + Zero + One + Div<Output = T>,
{
    type Output = Self;
    fn div(self, other: Self) -> Self {
        P::new(self.into_inner() / other.into_inner())
    }
}

impl<T> DivAssign for P<T>
where
    T: PartialOrd + Zero + One + DivAssign,
{
    fn div_assign(&mut self, other: Self) {
        self.0 /= other.into_inner();
    }
}

impl<T> FromPrimitive for P<T>
where
    T: PartialOrd + Zero + One + FromPrimitive,
{
    fn from_i64(n: i64) -> Option<Self> {
        match T::from_i64(n) {
            Some(p) => Some(P::new(p)),
            None => None,
        }
    }
    fn from_u64(n: u64) -> Option<Self> {
        match T::from_u64(n) {
            Some(p) => Some(P::new(p)),
            None => None,
        }
    }
}

impl<T> FromStr for P<T>
where
    T: PartialOrd + Zero + One + FromStr,
{
    type Err = <T as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let p = T::from_str(s)?;
        Ok(P::new(p))
    }
}

impl<T> Mul for P<T>
where
    T: PartialOrd + Zero + One,
{
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        P::new(self.into_inner() * other.into_inner())
    }
}

impl<T> MulAssign for P<T>
where
    T: PartialOrd + Zero + One + MulAssign,
{
    fn mul_assign(&mut self, other: Self) {
        self.0 *= other.into_inner();
    }
}

impl<T> MulAdd for P<T>
where
    T: PartialOrd + Zero + One + MulAdd<Output = T>,
{
    type Output = Self;
    fn mul_add(self, a: Self, b: Self) -> Self {
        P::new(self.into_inner().mul_add(a.into_inner(), b.into_inner()))
    }
}

impl<T> MulAddAssign for P<T>
where
    T: PartialOrd + Zero + One + MulAddAssign,
{
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        self.get_mut()
            .mul_add_assign(a.into_inner(), b.into_inner());
    }
}

impl<T> Num for P<T>
where
    T: Num + PartialOrd,
{
    type FromStrRadixErr = <T as Num>::FromStrRadixErr;
    fn from_str_radix(
        str: &str,
        radix: u32,
    ) -> Result<Self, <Self as num_traits::Num>::FromStrRadixErr> {
        let p = T::from_str_radix(str, radix)?;
        Ok(P::new(p))
    }
}

impl<T> NumCast for P<T>
where
    T: PartialOrd + Zero + One + NumCast,
{
    fn from<U: ToPrimitive>(n: U) -> Option<Self> {
        match T::from(n) {
            Some(p) => Some(P::new(p)),
            None => None,
        }
    }
}

impl<T> One for P<T>
where
    T: PartialOrd + Zero + One,
{
    fn one() -> Self {
        P::new_unchecked(T::one())
    }
}

impl<T> RelativeEq for P<T>
where
    T: PartialOrd + Zero + One + RelativeEq,
{
    fn default_max_relative() -> Self::Epsilon {
        T::default_max_relative()
    }
    fn relative_eq(
        &self,
        other: &Self,
        epsilon: Self::Epsilon,
        max_relative: Self::Epsilon,
    ) -> bool {
        self.get().relative_eq(other.get(), epsilon, max_relative)
    }
}

impl<T> Rem for P<T>
where
    T: PartialOrd + Zero + One + Rem<Output = T>,
{
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        P::new(self.into_inner() % other.into_inner())
    }
}

impl<T> RemAssign for P<T>
where
    T: PartialOrd + Zero + One + RemAssign,
{
    fn rem_assign(&mut self, other: Self) {
        self.0 %= other.into_inner();
    }
}

impl<T> Sub for P<T>
where
    T: PartialOrd + Zero + One + Sub<Output = T>,
{
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        P::new(self.into_inner() - other.into_inner())
    }
}

impl<T> SubAssign for P<T>
where
    T: PartialOrd + Zero + One + SubAssign,
{
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.into_inner();
    }
}

impl<T> SaturatingAdd for P<T>
where
    T: PartialOrd + Zero + One + SaturatingAdd,
{
    fn saturating_add(&self, other: &Self) -> Self {
        let one = T::one();
        let result = self.get().saturating_add(other.get());
        if result > one {
            P::new_unchecked(one)
        } else {
            P::new_unchecked(result)
        }
    }
}

impl<T> SaturatingMul for P<T>
where
    T: PartialOrd + Zero + One + SaturatingMul,
{
    fn saturating_mul(&self, other: &Self) -> Self {
        let one = T::one();
        let result = self.get().saturating_mul(other.get());
        if result > one {
            P::new_unchecked(one)
        } else {
            P::new_unchecked(result)
        }
    }
}

impl<T> SaturatingSub for P<T>
where
    T: PartialOrd + Zero + One + SaturatingSub,
{
    fn saturating_sub(&self, other: &Self) -> Self {
        let zero = T::zero();
        let result = self.get().saturating_sub(other.get());
        if result < zero {
            P::new_unchecked(zero)
        } else {
            P::new_unchecked(result)
        }
    }
}

impl<T> Sum for P<T>
where
    T: PartialOrd + Zero + One,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(P::<T>::zero(), |a, b| a + b)
    }
}

impl<'a, T> Sum<&'a P<T>> for P<T>
where
    T: PartialOrd + Zero + One + Clone,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Self>,
    {
        iter.fold(P::<T>::zero(), |a, b| a + b.clone())
    }
}

impl<T> ToPrimitive for P<T>
where
    T: PartialOrd + Zero + One + ToPrimitive,
{
    fn to_i64(&self) -> Option<i64> {
        self.get().to_i64()
    }
    fn to_u64(&self) -> Option<u64> {
        self.get().to_u64()
    }
}

impl<T> UlpsEq for P<T>
where
    T: PartialOrd + Zero + One + UlpsEq,
{
    fn default_max_ulps() -> u32 {
        T::default_max_ulps()
    }
    fn ulps_eq(&self, other: &Self, epsilon: Self::Epsilon, max_ulps: u32) -> bool {
        self.get().ulps_eq(other.get(), epsilon, max_ulps)
    }
}

impl<T> Unsigned for P<T> where T: PartialOrd + Zero + One + Num {}

impl<T> Zero for P<T>
where
    T: PartialOrd + Zero + One,
{
    fn zero() -> Self {
        P::new_unchecked(T::zero())
    }
    fn is_zero(&self) -> bool {
        self.get() == &T::zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;

    #[test]
    fn add_assign() {
        let mut q = P::new(0);
        let p = P::new(1);
        q += p.clone();
        assert_eq!(q, p);
    }

    #[test]
    fn distance() {
        let p = P::new(1);
        let q = P::new(0);
        assert_eq!(p.distance(q), P::new(1));
    }

    #[test_case(0,  |x| *x = 1, 1 ; "transforming zero to one")]
    #[test_case(0,  |x| *x = 2, 2 => panics ; "transforming zero to two")]
    fn map_inplace<T, F>(p: T, f: F, q: T)
    where
        T: PartialOrd + Zero + One + Debug,
        F: FnMut(&mut T),
    {
        let mut p = P::new(p);
        p.map_inplace(f);
        assert_eq!(P::new(q), p);
    }

    #[test_case(0,  |x| *x = 1, 1 ; "transforming zero to one")]
    #[test_case(0,  |x| *x = 2, 2 ; "transforming zero to two")]
    fn map_inplace_unchecked<T, F>(p: T, f: F, q: T)
    where
        T: PartialOrd + Zero + One + Debug,
        F: FnMut(&mut T),
    {
        let mut p = P::new(p);
        p.map_inplace_unchecked(f);
        assert_eq!(P::new_unchecked(q), p);
    }

    #[test_case(0, 1, 1, 1 ; "transforming zero to one")]
    #[test_case(0.4, 0.5, 0.5, 0.7 ; "floating")]
    fn mul_add_assign<T>(p: T, a: T, b: T, q: T)
    where
        T: PartialOrd + Zero + One + Debug + MulAddAssign,
    {
        let mut p = P::new(p);
        p.mul_add_assign(P::new(a), P::new(b));
        assert_eq!(P::new(q), p);
    }

    #[test]
    fn new() {
        let p = P::new(1);
        let inner: usize = *p.get();
        assert_eq!(inner, 1);
    }

    #[test]
    fn serialize() {
        let p = P::new(1);
        let s = ron::ser::to_string(&p).unwrap();
        assert_eq!("(1)".to_string(), s);
    }

    #[test]
    fn sum() {
        let probabilities = [P::new(0.3), P::new(0.4)];
        let sum = probabilities.iter().cloned().sum();
        assert_eq!(P::new(0.7), sum);
    }
}
