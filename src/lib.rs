use crate::extra::{AddExtra, ByRank, Extra};
use crate::mapping::{GrowableMapping, IdentityMapping, Mapping};
use crate::union::Union;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::error::Error;
use std::marker::PhantomData;
use thiserror::Error;

mod extra;
mod mapping;
mod union;

#[derive(Debug, Error)]
pub enum NewUnionFindError<P: Error, E: Error> {
    #[error("couldn't construct parents: {0}")]
    Parents(P),
    #[error("couldn't construct extra info: {0}")]
    Extra(E),
}

/// A union find datastructure. Note that this implementation clones elements a lot.
/// Generally, you should use the datastructure with small, preferably [`Copy`]able types,
/// like integers. However, arbitrary [`Clone`]+[`PartialEq`] types are possible.
pub struct UnionFind<T, M = HashMap<T, T>, E = ()> {
    parent: M,
    extra: E,
    phantom: PhantomData<T>,
}

type NewErr<M, E, T> =
    NewUnionFindError<<M as mapping::ParentMapping<T>>::Err, <E as Extra<T>>::ConstructErr>;

impl<T, M, E> UnionFind<T, M, E>
where
    M: mapping::ParentMapping<T>,
    T: Clone,
    E: Extra<T>,
{
    /// Constructs a new union find, using union by rank.
    pub fn new(elems: impl IntoIterator<Item = T> + Clone) -> Result<Self, NewErr<M, E, T>> {
        Ok(Self {
            parent: M::identity_map(elems.clone()).map_err(NewUnionFindError::Parents)?,
            extra: E::construct(elems).map_err(NewUnionFindError::Extra)?,
            phantom: Default::default(),
        })
    }
}

impl<T: PartialEq, M: Mapping<T, T>, E> UnionFind<T, M, E> {
    /// Find an element in the union find. Performs no path shortening,
    /// but can be used through an immutable reference.
    ///
    /// Use [`find_shorten`] for a more efficient find.
    pub fn find(&self, elem: &T) -> Option<&T> {
        let parent = self.parent.get(elem)?;
        if parent == elem {
            Some(parent)
        } else {
            let new_parent = self.find(parent)?;
            Some(new_parent)
        }
    }

    /// Find an element in the union find. Performs path shortening,
    /// which means you need mutable access to the union find.
    ///
    /// Use [`find`] for an immutable version.
    pub fn find_shorten(&mut self, elem: &T) -> Option<T>
    where
        T: Clone,
    {
        let parent = self.parent.get(elem)?.clone();
        if &parent == elem {
            Some(parent)
        } else {
            let new_parent = self.find_shorten(&parent)?;
            // path shortening
            self.parent.set(elem.clone(), new_parent.clone());
            Some(new_parent)
        }
    }
}

#[derive(Error, Debug)]
pub enum UnionError<Err> {
    #[error("the first element given as an argument to union was not found in the union find")]
    Elem1NotFound,

    #[error("the second element given as an argument to union was not found in the union find")]
    Elem2NotFound,

    #[error("could not union elements")]
    NotUnionable(Err),
}

pub enum UnionStatus {
    AlreadyEquivalent,
    PerformedUnion,
}

impl<T: PartialEq, ParentMapping: Mapping<T, T>> UnionFind<T, ParentMapping, ()>
where
    ParentMapping: Mapping<T, T>,
{
    /// union two elements in the union find
    pub fn union_by<U: Union<T>>(
        &mut self,
        elem1: &T,
        elem2: &T,
        union: U,
    ) -> Result<UnionStatus, UnionError<U::Err>>
    where
        T: Clone,
    {
        let parent1 = self.find_shorten(elem1).ok_or(UnionError::Elem1NotFound)?;
        let parent2 = self.find_shorten(elem2).ok_or(UnionError::Elem2NotFound)?;

        if parent1 == parent2 {
            return Ok(UnionStatus::AlreadyEquivalent);
        }

        let res = union
            .union(&parent1, &parent2)
            .map_err(UnionError::NotUnionable)?;

        self.parent.set(parent1, res.clone());
        self.parent.set(parent2, res);

        Ok(UnionStatus::PerformedUnion)
    }
}

#[derive(Error, Debug)]
pub enum UnionByRankError {
    #[error("the first element given as an argument to union was not found in the union find")]
    Elem1NotFound,

    #[error("the second element given as an argument to union was not found in the union find")]
    Elem2NotFound,
}

impl<T: PartialEq, ParentMapping: Mapping<T, T>, RankMapping>
    UnionFind<T, ParentMapping, ByRank<RankMapping, T>>
where
    ParentMapping: Mapping<T, T>,
    RankMapping: Mapping<T, usize>,
    T: Clone,
{
    /// union two elements in the union find
    pub fn union_by_rank(&mut self, elem1: &T, elem2: &T) -> Result<UnionStatus, UnionByRankError> {
        let parent1 = self
            .find_shorten(elem1)
            .ok_or(UnionByRankError::Elem1NotFound)?;
        let parent2 = self
            .find_shorten(elem2)
            .ok_or(UnionByRankError::Elem2NotFound)?;

        if parent1 == parent2 {
            return Ok(UnionStatus::AlreadyEquivalent);
        }

        let rank1 = self
            .extra
            .rank(&parent1)
            .ok_or(UnionByRankError::Elem1NotFound)?;
        let rank2 = self
            .extra
            .rank(&parent2)
            .ok_or(UnionByRankError::Elem2NotFound)?;

        match rank1.cmp(&rank2) {
            Ordering::Less => {
                self.parent.set(parent1, parent2);
            }
            Ordering::Equal => {
                self.parent.set(parent1, parent2.clone());
                self.extra.set_rank(parent2, rank2 + 1);
            }
            Ordering::Greater => {
                self.parent.set(parent2, parent1);
            }
        }

        Ok(UnionStatus::PerformedUnion)
    }
}

#[derive(Debug, Error)]
pub enum AddError<P: Error, E: Error> {
    #[error("couldn't construct parents: {0}")]
    Parents(P),
    #[error("couldn't construct extra info: {0}")]
    Extra(E),
}

type AddErr<E, T> = AddError<mapping::AddError, <E as AddExtra<T>>::AddErr>;

impl<T: Clone, M, E> UnionFind<T, M, E>
where
    M: IdentityMapping<T>,
    E: AddExtra<T>,
{
    pub fn add(&mut self, elem: T) -> Result<(), AddErr<E, T>> {
        self.parent
            .add_identity(elem.clone())
            .map_err(AddError::Parents)?;
        self.extra.add(elem).map_err(AddError::Extra)?;
        Ok(())
    }
}
