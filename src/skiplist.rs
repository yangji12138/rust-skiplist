//! A skiplist implementation which allows faster random access than a standard linked list.

use std::{
    cmp, cmp::Ordering, default, fmt, hash, hash::Hash, iter, ops, ops::Bound, ptr::NonNull,
};

use crate::{
    level_generator::{GeometricalLevelGenerator, LevelGenerator},
    skipnode::SkipNode,
};

pub use crate::skipnode::{IntoIter, Iter, IterMut};
use chain_common::digest::Digestible;
pub use blake2b_simd::{Hash as Blake2bHash, Params as Blake2bParams};
pub use primitive_types::*;
use crate::digest::{Proof, SubProof};

// ////////////////////////////////////////////////////////////////////////////
// SkipList
// ////////////////////////////////////////////////////////////////////////////

/// SkipList provides a way of storing elements and provides efficient way to
/// access, insert and remove nodes.
///
/// Unlike a standard linked list, the skiplist can skip ahead when trying to
/// find a particular index.
#[derive(Clone)]
pub struct SkipList<T:Digestible + PartialEq + Clone + Default> {
    // Storage, this is not sorted
    pub head: Box<SkipNode<T>>,
    pub len: usize,
    pub level_generator: GeometricalLevelGenerator,
}
/*
impl <T:Digestible + PartialEq + Clone> Copy for SkipList<T> {
}*/

impl <T:Digestible + PartialEq + Clone + Default> Digestible for SkipList<T> {
    fn to_digest(&self) -> H256 {
        let mut hasher = Blake2bParams::new();
        hasher.hash_length(32);
        hasher.to_state().update((*self.head).to_digest().as_bytes());
        hasher.to_state().update(&self.len.to_le_bytes());
        hasher.to_state().update(&self.level_generator.to_digest().as_bytes());
        H256::from_slice(hasher.to_state().finalize().as_bytes())    
    }
}

impl <T:Digestible + PartialEq + Clone + Default> SkipList<T> {
    fn eq(&self, other: &Self) -> bool {
        (*self.head == *other.head) && (self.len == other.len) && (self.level_generator == other.level_generator)
    }
}
/*
impl <T:Digestible + PartialEq + Clone> Default for SkipList<T> {
    fn default() -> Self {
        Self::new()
     }
}
*/


// ///////////////////////////////////////////////
// Inherent methods
// ///////////////////////////////////////////////

impl<T:Digestible + PartialEq + Clone + Default> SkipList<T> {
    /// Create a new skiplist with the default number of 16 levels.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist: SkipList<i64> = SkipList::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        let lg = GeometricalLevelGenerator::new(16, 1.0 / 2.0);
        SkipList {
            head: Box::new(SkipNode::head(lg.total())),
            len: 0,
            level_generator: lg,
        }
    }

    /// Constructs a new, empty skiplist with the optimal number of levels for
    /// the intended capacity.  Specifically, it uses `floor(log2(capacity))`
    /// number of levels, ensuring that only *a few* nodes occupy the highest
    /// level.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::with_capacity(100);
    /// skiplist.extend(0..100);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        let levels = cmp::max(1, (capacity as f64).log2().floor() as usize);
        let lg = GeometricalLevelGenerator::new(levels, 1.0 / 2.0);
        SkipList {
            head: Box::new(SkipNode::head(lg.total())),
            len: 0,
            level_generator: lg,
        }
    }

    /// Clears the skiplist, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// skiplist.clear();
    /// assert!(skiplist.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
        *self.head = SkipNode::head(self.level_generator.total());
    }

    /// Returns the number of elements in the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.len(), 10);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the skiplist contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.is_empty());
    ///
    /// skiplist.push_back(1);
    /// assert!(!skiplist.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Insert the element into the skiplist at the given index, shifting all
    /// subsequent nodes down.
    ///
    /// # Panics
    ///
    /// Panics if the insert index is greater than the length of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    ///
    /// skiplist.insert(0, 0);
    /// skiplist.insert(5, 1);
    /// assert_eq!(skiplist.len(), 2);
    /// assert!(!skiplist.is_empty());
    /// ```
    pub fn insert(&mut self, value: T, index: usize) {
        if index > self.len() {
            panic!("Index out of bounds.");
        }
        self.len += 1;
        let new_node = Box::new(SkipNode::new(value, self.level_generator.random()));
        self.head
            .insert_at(new_node, index)
            .unwrap_or_else(|_| panic!("No insertion position is found!"));
    }


    pub fn insert_with_order(&mut self, value: T, index: i32) {
        if index as usize > self.len() {
            panic!("Index out of bounds.");
        }
        self.len += 1;
        let new_node = Box::new(SkipNode::new(value, self.level_generator.determine(index)));
        self.head
            .insert_at(new_node, index as usize)
            .unwrap_or_else(|_| panic!("No insertion position is found!"));
    }

    /// Insert the element into the front of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.push_front(1);
    /// skiplist.push_front(2);
    /// ```
    pub fn push_front(&mut self, value: T) {
        self.insert(value, 0);
    }

    /// Insert the element into the back of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    /// ```
    pub fn push_back(&mut self, value: T) {
        let len = self.len();
        self.insert(value, len);
    }

    /// Provides a reference to the front element, or `None` if the skiplist is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.front().is_none());
    ///
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    /// assert_eq!(skiplist.front(), Some(&1));
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            self.get(0)
        }
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// skiplist is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.front().is_none());
    ///
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    /// assert_eq!(skiplist.front_mut(), Some(&mut 1));
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if self.is_empty() {
            None
        } else {
            self.get_mut(0)
        }
    }

    /// Provides a reference to the back element, or `None` if the skiplist is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.back().is_none());
    ///
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    /// assert_eq!(skiplist.back(), Some(&2));
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        let len = self.len();
        if len > 0 {
            self.get(len - 1)
        } else {
            None
        }
    }

    /// Provides a reference to the back element, or `None` if the skiplist is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.back().is_none());
    ///
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    /// assert_eq!(skiplist.back_mut(), Some(&mut 2));
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let len = self.len();
        if len > 0 {
            self.get_mut(len - 1)
        } else {
            None
        }
    }

    /// Provides a reference to the element at the given index, or `None` if the
    /// skiplist is empty or the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.get(0).is_none());
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.get(0), Some(&0));
    /// assert!(skiplist.get(10).is_none());
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.get_index(index).and_then(|node| node.item.as_ref())
    }

    #[inline]
    pub fn get_with_proof(&self, index: usize) -> (Option<&T>, Proof<T>) {
        let (value, nodes) = self.get_index_with_proof(index);
        let mut values: Vec<Option<T>> = Vec::new();
        let temp = value.and_then(|node| node.item.clone());
        values.push(temp);
        let mut nodehash: Vec<H256> = Vec::new();
        for elem in nodes.iter() {
            nodehash.push(elem.to_digest());
        }
        let subproof = SubProof::new(nodes.clone(), values, nodehash);
        let proof = Proof {
                       root: self.to_digest(),
                       subproof: subproof,};
        (value.and_then(|node| node.item.as_ref()), proof)
    }

    #[inline]
    pub fn get_with_subproof(&self, index: usize) -> (Option<&T>, Vec<SkipNode<T>>) {
        let (value, nodes) = self.get_index_with_proof(index);
        (value.and_then(|node| node.item.as_ref()), nodes)
    }

    /// Provides a mutable reference to the element at the given index, or
    /// `None` if the skiplist is empty or the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// assert!(skiplist.get_mut(0).is_none());
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.get_mut(0), Some(&mut 0));
    /// assert!(skiplist.get_mut(10).is_none());
    /// ```
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.get_index_mut(index)
            .and_then(|node| node.item.as_mut())
    }

    /// Removes the first element and returns it, or `None` if the sequence is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    ///
    /// assert_eq!(skiplist.pop_front(), Some(1));
    /// assert_eq!(skiplist.pop_front(), Some(2));
    /// assert!(skiplist.pop_front().is_none());
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(self.remove(0))
        }
    }

    /// Removes the last element and returns it, or `None` if the sequence is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.push_back(1);
    /// skiplist.push_back(2);
    ///
    /// assert_eq!(skiplist.pop_back(), Some(2));
    /// assert_eq!(skiplist.pop_back(), Some(1));
    /// assert!(skiplist.pop_back().is_none());
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        let len = self.len();
        if len > 0 {
            Some(self.remove(len - 1))
        } else {
            None
        }
    }

    /// Removes and returns an element with the given index.
    ///
    /// # Panics
    ///
    /// Panics is the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.remove(4), 4);
    /// assert_eq!(skiplist.remove(4), 5);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        if index >= self.len() {
            panic!("Index out of bounds.");
        } else {
            let node = self.head.remove_at(index).unwrap();
            self.len -= 1;
            node.into_inner().unwrap()
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// skiplist.retain(|&x| x%2 == 0);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.len -= self.head.retain(move |_, x| f(x));
    }

    /// Get an owning iterator over the entries of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.into_iter() {
    ///     println!("Value: {}", i);
    /// }
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(mut self) -> IntoIter<T> {
        let len = self.len();
        unsafe { IntoIter::from_head(&mut self.head, len) }
    }

    /// Creates an iterator over the entries of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.iter() {
    ///     println!("Value: {}", i);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<T> {
        unsafe { Iter::from_head(&self.head, self.len()) }
    }

    /// Creates an mutable iterator over the entries of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.iter_mut() {
    ///     println!("Value: {}", i);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        let len = self.len();
        unsafe { IterMut::from_head(&mut self.head, len) }
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// skiplist, starting at min, and ending at max. If min is `Unbounded`,
    /// then it will be treated as "negative infinity", and if max is
    /// `Unbounded`, then it will be treated as "positive infinity".  Thus
    /// range(Unbounded, Unbounded) will yield the whole collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    /// use std::ops::Bound::{Included, Unbounded};
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.range(Included(3), Included(7)) {
    ///     println!("Value: {}", i);
    /// }
    /// assert_eq!(Some(&4), skiplist.range(Included(4), Unbounded).next());
    /// ```
    pub fn range(&self, min: Bound<usize>, max: Bound<usize>) -> Iter<T> {
        let first = match min {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i + 1,
            Bound::Unbounded => 0,
        };
        let last = match max {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i - 1,
            Bound::Unbounded => self.len() - 1,
        };
        self.iter_range(first, last)
    }

    /// Constructs a mutable double-ended iterator over a sub-range of elements
    /// in the skiplist, starting at min, and ending at max. If min is
    /// `Unbounded`, then it will be treated as "negative infinity", and if max
    /// is `Unbounded`, then it will be treated as "positive infinity".  Thus
    /// range(Unbounded, Unbounded) will yield the whole collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    /// use std::ops::Bound::{Included, Unbounded};
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.range_mut(Included(3), Included(7)) {
    ///     println!("Value: {}", i);
    /// }
    /// assert_eq!(Some(&mut 4), skiplist.range_mut(Included(4), Unbounded).next());
    /// ```
    pub fn range_mut(&mut self, min: Bound<usize>, max: Bound<usize>) -> IterMut<T> {
        let first = match min {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i + 1,
            Bound::Unbounded => 0,
        };
        let last = match max {
            Bound::Included(i) => i,
            Bound::Excluded(i) => i - 1,
            Bound::Unbounded => self.len() - 1,
        };
        self.iter_range_mut(first, last)
    }
}

impl<T:Digestible + PartialEq + Clone + Default> SkipList<T>
where
    T: PartialEq,
{
    /// Returns true if the value is contained in the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.extend(0..10);
    /// assert!(skiplist.contains(&4));
    /// assert!(!skiplist.contains(&15));
    /// ```
    pub fn contains(&self, value: &T) -> bool {
        self.iter().any(|val| val.eq(value))
    }

    /// Removes all consecutive repeated elements in the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::SkipList;
    ///
    /// let mut skiplist = SkipList::new();
    /// skiplist.push_back(0);
    /// skiplist.push_back(0);
    /// assert_eq!(skiplist.len(), 2);
    /// skiplist.dedup();
    /// assert_eq!(skiplist.len(), 1);
    /// ```
    pub fn dedup(&mut self) {
        let removed = self
            .head
            .retain(|prev, current| prev.map_or(true, |prev| !prev.eq(current)));
        self.len -= removed;
    }
}

// ///////////////////////////////////////////////
// Internal methods
// ///////////////////////////////////////////////

impl<T:Digestible + PartialEq + Clone + Default> SkipList<T> {
    /// Checks the integrity of the skiplist.
    #[allow(dead_code)]
    fn check(&self) {
        self.head.check();
    }

    /// Makes an iterator between [begin, end]
    fn iter_range(&self, first_idx: usize, last_idx: usize) -> Iter<T> {
        if first_idx > last_idx {
            return Iter {
                first: None,
                last: None,
                size: 0,
            };
        }
        let first = self.get_index(first_idx);
        let last = self.get_index(last_idx);
        if first.is_some() && last.is_some() {
            Iter {
                first,
                last,
                size: last_idx - first_idx + 1,
            }
        } else {
            Iter {
                first: None,
                last: None,
                size: 0,
            }
        }
    }

    /// Makes an iterator between [begin, end]
    fn iter_range_mut(&mut self, first_idx: usize, last_idx: usize) -> IterMut<T> {
        if first_idx > last_idx {
            return IterMut {
                first: None,
                last: None,
                size: 0,
            };
        }
        let last = self.get_index_mut(last_idx).and_then(|p| NonNull::new(p));
        let first = self.get_index_mut(first_idx);
        if first.is_some() && last.is_some() {
            IterMut {
                first,
                last,
                size: last_idx - first_idx + 1,
            }
        } else {
            IterMut {
                first: None,
                last: None,
                size: 0,
            }
        }
    }

    /// Gets a pointer to the node with the given index.
    pub fn get_index(&self, index: usize) -> Option<&SkipNode<T>> {
        if self.len() <= index {
            None
        } else {
            self.head.advance(index + 1)
        }
    }

    /// Gets a pointer to the node with the given index.
    pub fn get_index_with_proof(&self, index: usize) -> (Option<&SkipNode<T>>, Vec<SkipNode<T>>) {
        if self.len() <= index {
            let proof : Vec<SkipNode<T>> = Vec::new();
            (None, proof)
        } else {
            self.head.advance_with_proof(index + 1)
        }
    }

    fn get_index_mut(&mut self, index: usize) -> Option<&mut SkipNode<T>> {
        if self.len() <= index {
            None
        } else {
            self.head.advance_mut(index + 1)
        }
    }
}

impl<T:Digestible + PartialEq + Clone + Default> SkipList<T>
where
    T: fmt::Debug,
{
    /// Prints out the internal structure of the skiplist (for debugging
    /// purposes).
    #[allow(dead_code)]
    fn debug_structure(&self) {
        unsafe {
            let mut node = self.head.as_ref();
            let mut rows: Vec<_> = iter::repeat(String::new())
                .take(self.level_generator.total())
                .collect();

            loop {
                let value = if let Some(ref v) = node.item {
                    format!("> [{:?}]", v)
                } else {
                    "> []".to_string()
                };

                let max_str_len = format!("{} -{}-", value, node.links_len[node.level]).len() + 1;

                let mut lvl = self.level_generator.total();
                while lvl > 0 {
                    lvl -= 1;

                    let mut value_len = if lvl <= node.level {
                        format!("{} -{}-", value, node.links_len[lvl])
                    } else {
                        format!("{} -", value)
                    };
                    for _ in 0..(max_str_len - value_len.len()) {
                        value_len.push('-');
                    }

                    let mut dashes = String::new();
                    for _ in 0..value_len.len() {
                        dashes.push('-');
                    }

                    if lvl <= (*node).level {
                        rows[lvl].push_str(value_len.as_ref());
                    } else {
                        rows[lvl].push_str(dashes.as_ref());
                    }
                }

                if let Some(next) = node.links[0].and_then(|p| p.as_ptr().as_ref()) {
                    node = next;
                } else {
                    break;
                }
            }

            for row in rows.iter().rev() {
                println!("{}", row);
            }
        }
    }
}

// ///////////////////////////////////////////////
// Trait implementation
// ///////////////////////////////////////////////

unsafe impl<T: Send + Digestible + PartialEq + Clone + Default> Send for SkipList<T> {}
unsafe impl<T: Sync + Digestible + PartialEq + Clone + Default> Sync for SkipList<T> {}

impl<T:Digestible + PartialEq + Clone + Default> default::Default for SkipList<T> {
    fn default() -> SkipList<T> {
        SkipList::new()
    }
}


/// This implementation of PartialEq only checks that the *values* are equal; it
/// does not check for equivalence of other features (such as the ordering
/// function and the node levels). Furthermore, this uses `T`'s implementation
/// of PartialEq and *does not* use the owning skiplist's comparison function.
impl<A:Digestible + PartialEq + Clone + Default, B:Digestible + PartialEq + Clone + Default> cmp::PartialEq<SkipList<B>> for SkipList<A>
where
    A: cmp::PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &SkipList<B>) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }
    #[allow(clippy::partialeq_ne_impl)]
    #[inline]
    fn ne(&self, other: &SkipList<B>) -> bool {
        self.len != other.len || self.iter().ne(other)
    }
}

impl<T:Digestible + PartialEq + Clone + Default> cmp::Eq for SkipList<T> where T: cmp::Eq {}

impl<A:Digestible + PartialEq + Clone + Default, B:Digestible + PartialEq + Clone + Default> cmp::PartialOrd<SkipList<B>> for SkipList<A>
where
    A: cmp::PartialOrd<B>,
{
    #[inline]
    fn partial_cmp(&self, other: &SkipList<B>) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T:Digestible + PartialEq + Clone + Default> Ord for SkipList<T>
where
    T: cmp::Ord,
{
    #[inline]
    fn cmp(&self, other: &SkipList<T>) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T:Digestible + PartialEq + Clone + Default> Extend<T> for SkipList<T> {
    #[inline]
    fn extend<I: iter::IntoIterator<Item = T>>(&mut self, iterable: I) {
        let iterator = iterable.into_iter();
        for element in iterator {
            self.push_back(element);
        }
    }
}

impl<T:Digestible + PartialEq + Clone + Default> ops::Index<usize> for SkipList<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get(index).expect("Index out of range")
    }
}

impl<T:Digestible + PartialEq + Clone + Default> ops::IndexMut<usize> for SkipList<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).expect("Index out of range")
    }
}

impl<T:Digestible + PartialEq + Clone + Default> fmt::Debug for SkipList<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        for (i, entry) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", entry)?;
        }
        write!(f, "]")
    }
}

impl<T:Digestible + PartialEq + Clone + Default> fmt::Display for SkipList<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        for (i, entry) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", entry)?;
        }
        write!(f, "]")
    }
}

impl<T:Digestible + PartialEq + Clone + Default> iter::IntoIterator for SkipList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        self.into_iter()
    }
}
impl<'a, T:Digestible + PartialEq + Clone + Default> iter::IntoIterator for &'a SkipList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}
impl<'a, T:Digestible + PartialEq + Clone + Default> iter::IntoIterator for &'a mut SkipList<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T:Digestible + PartialEq + Clone + Default> iter::FromIterator<T> for SkipList<T> {
    #[inline]
    fn from_iter<I>(iter: I) -> SkipList<T>
    where
        I: iter::IntoIterator<Item = T>,
    {
        let mut skiplist = SkipList::new();
        skiplist.extend(iter);
        skiplist
    }
}

impl<T: Hash + Digestible + PartialEq + Clone + Default> Hash for SkipList<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        for elt in self {
            elt.hash(state);
        }
    }
}

