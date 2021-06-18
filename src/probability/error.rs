use core::fmt::Debug;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(
    Copy, Clone, Debug, Deserialize, Eq, Error, Hash, Ord, PartialEq, PartialOrd, Serialize,
)]
pub enum Bound<T>
where
    T: Debug,
{
    #[error("upper bound violated (found {0:?})")]
    Upper(T),
    #[error("lower bound violated (found {0:?})")]
    Lower(T),
}
