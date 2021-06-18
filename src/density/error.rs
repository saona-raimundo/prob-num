use core::fmt::Debug;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(
    Copy, Clone, Debug, Deserialize, Eq, Error, Hash, Ord, PartialEq, PartialOrd, Serialize,
)]
pub enum Bound<T: 'static>
where
    T: Debug,
{
    #[error("total mass errors")]
    TotalMass {
        #[from]
        source: TotalMass<T>,
    },
    #[error("some probability errors")]
    Element {
        #[from]
        source: crate::probability::Bound<T>,
    },
    #[error("empty probability mass function")]
    Empty,
}

#[derive(
    Copy, Clone, Debug, Deserialize, Eq, Error, Hash, Ord, PartialEq, PartialOrd, Serialize,
)]
pub enum TotalMass<T>
where
    T: Debug,
{
    #[error("total mass is more than one (found {0:?})")]
    TooMuch(T),
    #[error("total mass is less than one (found {0:?})")]
    TooLittle(T),
}
