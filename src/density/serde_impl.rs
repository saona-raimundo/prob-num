use crate::{D, P};
use core::fmt::Debug;
use num_traits::identities::{One, Zero};
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Deserializer, Serialize, Serializer,
};
use std::{convert::TryInto, marker::PhantomData};

// DESERIALIZE
//
struct ArrayVisitor<T, const N: usize>(PhantomData<T>);
impl<'de, T, const N: usize> Visitor<'de> for ArrayVisitor<T, N>
where
    T: PartialOrd + Zero + One + Copy + Deserialize<'de>,
{
    type Value = [P<T>; N];
    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a density of length {}", N)
    }
    #[inline]
    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut data = Vec::with_capacity(N);
        for _ in 0..N {
            match (seq.next_element())? {
                Some(val) => data.push(val),
                None => return Err(serde::de::Error::invalid_length(N, &self)),
            }
        }
        match data.try_into() {
            Ok(arr) => Ok(arr),
            Err(_) => unreachable!(),
        }
    }
}

struct __Visitor<'de, T, const N: usize>
where
    T: PartialOrd + Zero + One + Copy + Deserialize<'de>,
{
    marker: PhantomData<D<T, N>>,
    lifetime: PhantomData<&'de ()>,
}
impl<'de, T, const N: usize> Visitor<'de> for __Visitor<'de, T, N>
where
    T: PartialOrd + Zero + One + Copy + Deserialize<'de>,
{
    type Value = D<T, N>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a density of length {}", N)
    }

    #[inline]
    fn visit_newtype_struct<De>(self, de: De) -> Result<Self::Value, De::Error>
    where
        De: Deserializer<'de>,
    {
        let probabilities: [P<T>; N] =
            de.deserialize_tuple(N, ArrayVisitor::<T, N>(PhantomData))?;
        Ok(D(probabilities))
    }
}

impl<'de, T, const N: usize> Deserialize<'de> for D<T, N>
where
    T: PartialOrd + Zero + One + Copy + Debug + Deserialize<'de>,
{
    fn deserialize<De>(deserializer: De) -> Result<Self, De::Error>
    where
        De: Deserializer<'de>,
    {
        Deserializer::deserialize_newtype_struct(
            deserializer,
            "D",
            __Visitor {
                marker: PhantomData::<D<T, N>>,
                lifetime: PhantomData,
            },
        )
    }
}

// SERIALIZE
//
// To serialize [P<T>; N], since constant generics do not implement Serialize yet
// from: https://github.com/serde-rs/serde/issues/1937
struct __SerializeWith<T, const N: usize>
where
    T: PartialOrd + Zero + One + Copy + Serialize,
{
    value: [P<T>; N],
    phantom: PhantomData<D<T, N>>,
}
impl<T, const N: usize> Serialize for __SerializeWith<T, N>
where
    T: PartialOrd + Zero + One + Copy + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(N)?;
        for item in &self.value {
            s.serialize_element(item)?;
        }
        s.end()
    }
}

impl<T, const N: usize> Serialize for D<T, N>
where
    T: PartialOrd + Zero + One + Copy + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_newtype_struct(
            "D",
            &__SerializeWith {
                value: self.0,
                phantom: PhantomData::<D<T, N>>,
            },
        )
    }
}
