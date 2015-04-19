/// Implements an ordered map as a BurstTrie. It's a very fast Trie variant specialized for Str types.
///
/// This structure achieves better performance than a BTree implementations for common operations while
/// still allowing range scanning and ordered iteration. Performance wise it's usually 50+% faster than
/// the std lib BTreeMap for random keys and pulls ahead rapdily if keys have common prefixes.
///
/// It's specialized for string keys, specifically ASCII or UTF-8.
///
/// The Burst Trie was originaly described by S. Heinz.
/// You can find the original paper in the internet by it's title
/// "Burst Tries: A Fast, Efficient Data Structure for String Keys"

use std::mem;
use std::slice;
use std::vec;
use std::ptr;
use std::convert::AsRef;
// use std::collections::Bound;
// use std::collections::VecDeque;
use std::cmp::Ordering;
use std::default::Default;
use std::ops::{Index, IndexMut};
use std::iter::Map;
use std::rc::Rc;
use std::cell::UnsafeCell;

const ALPHABET_SIZE: usize = 128; // ascii AND utf-8 compatible
const BUCKET_SIZE: usize = 64;

/// An BurstTrie implementation of an ordered map. Specialized for Str types.
///
/// See module level docs for details.
pub struct BurstTrieMap<K, V> where K: AsRef<str> {
    root: BurstTrieNode<K, V>,
    len: usize
}

enum BurstTrieNode<K, V> where K: AsRef<str> {
    Empty,
    Hybrid(Rc<UnsafeCell<BucketNode<K, V>>>),
    Bucket(BucketNode<K, V>),
    Access(AccessNode<K, V>)
}

struct BucketNode<K, V> where K: AsRef<str> {
    items: Vec<(K, V)>
}

struct AccessNode<K, V> where K: AsRef<str> {
    nodes: Box<[BurstTrieNode<K, V>; ALPHABET_SIZE]>,
    terminator: Option<(K, V)>
}

impl<K, V> BurstTrieMap<K, V> where K: AsRef<str> {
    
    /// Returns a new empty BurstTrieMap
    pub fn new() -> BurstTrieMap<K, V> {
        BurstTrieMap {
            root: BurstTrieNode::Access(AccessNode::new()),
            len: 0,
        }
    }


    /// Inserts a key-value pair from the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert("a", 0u32);
    /// assert_eq!(a.len(), 1);
    /// assert_eq!(a.insert("a", 1), Some(0));
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if let BurstTrieNode::Access(ref mut access) = self.root {
            let opt_old_value = access.insert(key, value, 0);
            if opt_old_value.is_none() {
                self.len += 1;
            }
            opt_old_value
        } else {
            unreachable!();
        }
    }


    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed form must match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// a.insert("a", 0);
    /// assert_eq!(a.get("a"), Some(&0));
    /// assert_eq!(a.get("b"), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V> where Q: AsRef<str> {
        if let BurstTrieNode::Access(ref access) = self.root {
            access.get(key, 0)
        } else {
            unreachable!();
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed form must match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// a.insert("a", 0);
    /// assert_eq!(a.get("a"), Some(&0));
    /// assert_eq!(a.get("b"), None);
    /// if let Some(mv) = a.get_mut("a") {
    ///     *mv = 1;
    /// }
    /// assert_eq!(a.get("a"), Some(&1));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V> where Q: AsRef<str> {
        if let BurstTrieNode::Access(ref mut access) = self.root {
            access.get_mut(key, 0)
        } else {
            unreachable!();
        }
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// a.insert("a", 0);
    /// assert_eq!(a.contains_key("a"), true);
    /// assert_eq!(a.contains_key("b"), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool where Q: AsRef<str> {
        self.get(key).is_some()
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert("a", 0u32);
    /// assert_eq!(a.len(), 1);
    /// assert_eq!(a.remove("a"), Some(0));
    /// assert_eq!(a.len(), 0);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V> where Q: AsRef<str> {
        if let BurstTrieNode::Access(ref mut access) = self.root {
            let opt_old_value = access.remove(key, 0);
            if opt_old_value.is_some() {
                self.len -= 1;
            }
            opt_old_value
        } else {
            unreachable!();
        }
    }

    /// Return the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert("a", 0u32);
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns *true* if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Clears all elements from the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use burst_trie::BurstTrieMap;
    ///
    /// let mut a = BurstTrieMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert("a", 0u32);
    /// assert_eq!(a.len(), 1);
    /// a.clear();
    /// assert_eq!(a.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.root = BurstTrieNode::Access(AccessNode::new());
        self.len = 0;
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            stack: vec![&self.root],
            bucket_iter: None,
            remaining_len: self.len
        }
    }
    
    pub fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            stack: vec![self.root],
            bucket_iter: None,
            remaining_len: self.len
        }
    }

    pub fn keys<'a>(&'a self) -> Map<Iter<K, V>, fn((&'a K, &'a V)) -> &'a K> {
        #[inline(always)]
        fn map_fn<'a, K, V>(kv: (&'a K, &'a V)) -> &'a K {
            &kv.0
        }
        self.iter().map(map_fn)
    }

    pub fn values<'a>(&'a self) -> Map<Iter<K, V>, fn((&'a K, &'a V)) -> &'a V> {
        #[inline(always)]
        fn map_fn<'a, K, V>(kv: (&'a K, &'a V)) -> &'a V {
            &kv.1
        }
        self.iter().map(map_fn)
    }

    // pub fn range<'a, Q: ?Sized>(&'a self, min: Bound<&'a Q>, max: Bound<&'a Q>) -> Range<K, V, Q: ?Sized> where Q: AsRef<str> {
    //     Range::new(&self.root, min, max)
    // }
}

impl<K, V> PartialEq for BurstTrieNode<K, V> where K: AsRef<str> {
    fn eq(&self, other: &Self) -> bool {
        extern { fn memcmp(s1: *const i8, s2: *const i8, n: usize) -> i32; }
        unsafe { memcmp(mem::transmute(self), mem::transmute(other), mem::size_of::<Self>()) == 0 }
    }
}

impl<K, V> BucketNode<K, V> where K: AsRef<str> {
    fn new() -> BucketNode<K, V> {
        BucketNode {
            items: Vec::new()
        }
    }

    #[inline]
    fn insert(&mut self, key: K, value: V, depth: usize) -> Option<V> {
        // optimize insertions at the end
        // helps in seq insert and node bursting
        let seq_insert = match self.items.last_mut() {
            Some(&mut (ref last_key, ref mut last_value)) =>
                match last_key.as_ref()[depth..].cmp(&key.as_ref()[depth..]) {
                    Ordering::Equal => {
                        return Some(mem::replace(last_value, value));
                    },
                    Ordering::Less => true,
                    Ordering::Greater => false
                },
            _ => true
        };

        if seq_insert {
            self.items.push((key, value));
        } else {
            // binary search doesn't have to check the last element due to the previous
            let res_bs = self.items[..self.items.len() - 1].binary_search_by(|other| {
                other.0.as_ref()[depth..].cmp(&key.as_ref()[depth..])
            });
            match res_bs {
                Ok(pos) => {
                    let old_value = unsafe { self.items.get_unchecked_mut(pos) };
                    return Some(mem::replace(&mut old_value.1, value));
                },
                Err(pos) => {
                    self.items.insert(pos, (key, value));
                },
            };
        }

        None
    }


    #[inline]
    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<V> where Q: AsRef<str> {
        let res_bs = self.items.binary_search_by(|other| {
            other.0.as_ref()[depth..].cmp(&key.as_ref()[depth..])
        });
        match res_bs {
            Ok(pos) => Some(self.items.remove(pos).1),
            Err(_) => None
        }
    }

    #[inline]
    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: AsRef<str> {
        // FIXME: binary search is doing bounds checking internally ;/
        // FIXME: Needs a macro to generate (i)mutable versions
        let res_bs = self.items.binary_search_by(|other| {
            other.0.as_ref()[depth..].cmp(&key.as_ref()[depth..])
        });
        if let Ok(pos) = res_bs {
            Some(unsafe { &self.items.get_unchecked(pos).1 })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<&mut V> where Q: AsRef<str> {
        // FIXME: binary search is doing bounds checking internally ;/
        // FIXME: Needs a macro to generate (i)mutable versions
        let res_bs = self.items.binary_search_by(|other| {
            other.0.as_ref()[depth..].cmp(&key.as_ref()[depth..])
        });
        if let Ok(pos) = res_bs {
            Some(unsafe { &mut self.items.get_unchecked_mut(pos).1 })
        } else {
            None
        }
    }

    #[inline]
    fn need_split(&self) -> bool {
        self.items.len() > BUCKET_SIZE
    }

    fn find_split(&self, depth: usize, lo: usize, _: usize) -> (usize, usize) {
        use std::u8::MAX as U8MAX;
        debug_assert!(ALPHABET_SIZE < U8MAX as usize);
        let mut alphabet_counter = [0u8; ALPHABET_SIZE];
        let mut total_counter = 0;
        let mut last_alph_idx = 0;
        for &(ref k, _) in &self.items {
            let alph_idx = k.as_ref().as_bytes()[depth] as usize;
            if total_counter > BUCKET_SIZE / 2 && alphabet_counter[alph_idx] == 0  {
                return (last_alph_idx + 1, total_counter);
            }
            alphabet_counter[alph_idx] += 1;
            total_counter += 1;
            last_alph_idx = alph_idx;
        }

        if last_alph_idx == lo {
            (last_alph_idx + 1, alphabet_counter[last_alph_idx] as usize)
        } else {
            (last_alph_idx, total_counter - alphabet_counter[last_alph_idx] as usize)
        }
    }
}

impl<K, V> AccessNode<K, V> where K: AsRef<str> {
    fn new() -> AccessNode<K, V> {
        let mut access = AccessNode {
            nodes: Box::new(unsafe { mem::zeroed() }),
            terminator: None
        };
        let node = Rc::new(UnsafeCell::new(BucketNode::new()));
        for i in (0..ALPHABET_SIZE) {
            access.nodes[i] = BurstTrieNode::Hybrid(node.clone());
        }
        access
    }

    fn from_pure_bucket(mut bucket: BucketNode<K,V>, depth: usize) -> AccessNode<K, V> {
        let mut access = AccessNode {
            nodes: Box::new(unsafe { mem::zeroed() }),
            terminator: None
        };

        if bucket.items[0].0.as_ref().len() == depth {
            access.terminator = Some(bucket.items.remove(0));
        }

        let node = Rc::new(UnsafeCell::new(bucket));
        for i in (0..ALPHABET_SIZE) {
            access.nodes[i] = BurstTrieNode::Hybrid(node.clone());
        }

        access
    }

    fn split(&mut self, node_idx: usize, depth: usize) {
        let old_node = match self.nodes[node_idx] {
            ref mut node @ BurstTrieNode::Bucket(_) => {
                if let BurstTrieNode::Bucket(bucket) = mem::replace(node, BurstTrieNode::Empty) {
                    let mut access = AccessNode::from_pure_bucket(bucket, depth + 1);
                    access.split(0, depth + 1);
                    mem::replace(node, BurstTrieNode::Access(access));
                    return;
                }
                unreachable!();
            },
            ref mut node @ BurstTrieNode::Hybrid(_) => {
                mem::replace(node, BurstTrieNode::Empty)
            },
            _ => unreachable!()
        };

        let mut lo = 0;
        let mut hi = ALPHABET_SIZE - 1;
        let mut idx = node_idx as isize - 1; // must signed to prevent wraping when node_idx = 0
        while idx as isize > 0 {
            if &self.nodes[idx as usize] != &old_node {
                lo = idx as usize + 1;
                break;
            }
            idx -= 1;
        }
        let mut idx = node_idx + 1;
        while idx < ALPHABET_SIZE {
            if &self.nodes[idx] != &old_node {
                hi = idx - 1;
                break;
            }
            idx += 1;
        }

        let old_bucket_rc_cell = if let BurstTrieNode::Hybrid(bucket_rc_cell) = old_node {
            bucket_rc_cell 
        } else {
            unreachable!();
        };

        let (nodes_split, bucket_split) = unsafe {
            (& *old_bucket_rc_cell.get()).find_split(depth, lo, hi)
        };

        // move stuff from left bucket to right bucket
        let mut right_bucket = BucketNode::new();
        unsafe {
            let old_bucket = &mut *old_bucket_rc_cell.get();
            right_bucket.items.reserve(old_bucket.items.len() - bucket_split);
            for item in &old_bucket.items[bucket_split..] {
                right_bucket.items.push(ptr::read(item as *const (_, _)));
            }
            old_bucket.items.set_len(bucket_split);
        }

        // right bucket
        if hi == nodes_split {
            self.nodes[hi] = BurstTrieNode::Bucket(right_bucket);
        } else {
            let new_node = Rc::new(UnsafeCell::new(right_bucket));
            for idx in (nodes_split..hi + 1) {
                self.nodes[idx] = BurstTrieNode::Hybrid(new_node.clone());
            }
        }

        // left bucket
        if lo + 1 == nodes_split {
            let left_bucket = unsafe { mem::replace(&mut *old_bucket_rc_cell.get(), BucketNode::new()) };
            self.nodes[lo] = BurstTrieNode::Bucket(left_bucket);
        } else {
            let new_node = old_bucket_rc_cell;
            for idx in (lo..nodes_split) {
                self.nodes[idx] = BurstTrieNode::Hybrid(new_node.clone());
            }
        }

        if (bucket_split == 0 && node_idx >= nodes_split) || (bucket_split > BUCKET_SIZE && node_idx < nodes_split) {
            self.split(node_idx, depth);
        }
    }

    #[inline]
    fn insert(&mut self, key: K, value: V, depth: usize) -> Option<V> {
        // depth is always <= key.len
        if depth < key.as_ref().len() {
            let idx = key.as_ref().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            match self.nodes[idx] {
                BurstTrieNode::Access(ref mut access) =>
                    return access.insert(key, value, depth + 1),
                BurstTrieNode::Bucket(ref mut bucket) => {
                    let result = bucket.insert(key, value, depth + 1);
                    if ! bucket.need_split() {
                        return result
                    }
                },
                BurstTrieNode::Hybrid(ref mut bucket_rc_cell) => {
                    let bucket = unsafe { (&mut *bucket_rc_cell.get()) };
                    let result = bucket.insert(key, value, depth);
                    if ! bucket.need_split() {
                        return result
                    }
                },
                _ => unreachable!()
            }
            self.split(idx, depth);
            None
        } else if let Some((_, ref mut old_value)) = self.terminator {
            Some(mem::replace(old_value, value))
        } else {
            self.terminator = Some((key, value));
            None
        }
    }

    #[inline]
    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<V> where Q: AsRef<str> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            match self.nodes[idx] {
                BurstTrieNode::Access(ref mut access) =>
                    access.remove(key, depth + 1),
                BurstTrieNode::Bucket(ref mut bucket) =>
                    bucket.remove(key, depth + 1),
                BurstTrieNode::Hybrid(ref mut bucket_rc_cell) =>
                    unsafe { (&mut *bucket_rc_cell.get()).remove(key, depth) },
                _ => unreachable!()
            }
        } else if let Some((_, old_value)) = self.terminator.take() {
            Some(old_value)
        } else {
            None
        }
    }

    // #[inline]
    // fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: AsRef<str> {
    //     if depth < key.as_ref().len() {
    //         let idx = key.as_ref().as_bytes()[depth] as usize;
    //         debug_assert!(idx < ALPHABET_SIZE);
    //         match self.nodes[idx] {
    //             BurstTrieNode::Access(ref access) =>
    //                 access.get(key, depth + 1),
    //             BurstTrieNode::Bucket(ref bucket) =>
    //                 bucket.get(key, depth + 1),
    //             BurstTrieNode::Hybrid(ref bucket_rc_cell) =>
    //                 unsafe { (& *bucket_rc_cell.get()).get(key, depth) },
    //             _ => unreachable!()
    //         }
    //     } else {
    //         if let Some((_, ref v)) = self.terminator {
    //             Some(v)
    //         } else {
    //             None
    //         }
    //     }
    // }
    #[inline]
    fn get<Q: ?Sized>(&self, key: &Q, mut depth: usize) -> Option<&V> where Q: AsRef<str> {
        let mut this_access = self;

        loop {
            if depth < key.as_ref().len() {
                let idx = key.as_ref().as_bytes()[depth] as usize;
                debug_assert!(idx < ALPHABET_SIZE);
                match this_access.nodes[idx] {
                    BurstTrieNode::Access(ref access) => {
                        this_access = access;
                        depth += 1;
                    },
                    BurstTrieNode::Bucket(ref bucket) =>
                        return bucket.get(key, depth + 1),
                    BurstTrieNode::Hybrid(ref bucket_rc_cell) =>
                        return unsafe { (& *bucket_rc_cell.get()).get(key, depth) },
                    _ => unreachable!()
                }
            } else if let Some((_, ref v)) = this_access.terminator {
                return Some(v)
            } else {
                return None
            }
        }
    }

    #[inline]
    fn get_mut<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<&mut V> where Q: AsRef<str> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            match self.nodes[idx] {
                BurstTrieNode::Access(ref mut access) =>
                    access.get_mut(key, depth + 1),
                BurstTrieNode::Bucket(ref mut bucket) =>
                    bucket.get_mut(key, depth + 1),
                BurstTrieNode::Hybrid(ref mut bucket_rc_cell) =>
                    unsafe { (&mut *bucket_rc_cell.get()).get_mut(key, depth) },
                _ => unreachable!()
            }
        } else {
            if let Some((_, ref mut v)) = self.terminator {
                Some(v)
            } else {
                None
            }
        }
    }
}

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for BurstTrieMap<K, V> where K: AsRef<str>, Q: AsRef<str> {
    type Output = V;
    #[inline]
    fn index(&self, index: &Q) -> &V {
        self.get(index).unwrap()
    }
}

impl<'a, K, V, Q: ?Sized> IndexMut<&'a Q> for BurstTrieMap<K, V> where K: AsRef<str>, Q: AsRef<str> {
    #[inline]
    fn index_mut(&mut self, index: &Q) -> &mut V {
        self.get_mut(index).unwrap()
    }
}

impl<K, V> Default for BurstTrieMap<K, V> where K: AsRef<str> {
    #[inline]
    fn default() -> BurstTrieMap<K, V> { BurstTrieMap::new() }
}

pub struct Iter<'a, K: 'a, V: 'a> where K: AsRef<str> {
    stack: Vec<&'a BurstTrieNode<K, V>>,
    bucket_iter: Option<slice::Iter<'a, (K, V)>>,
    remaining_len: usize
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> where K: AsRef<str> {}

impl<'a, K, V> Iterator for Iter<'a, K, V> where K: AsRef<str> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if let Some(ref mut iter) = self.bucket_iter {
            let next = iter.next();
            if let Some(&(ref key, ref value)) = next {
                self.remaining_len -= 1;
                return Some((key, value));
            }
        }

        while let Some(node) = self.stack.pop() {
            match *node {
                BurstTrieNode::Bucket(ref bucket) => {
                    let mut iter = bucket.items.iter();
                    let next = iter.next();
                    mem::replace(&mut self.bucket_iter, Some(iter)); 
                    if let Some(&(ref key, ref value)) = next {
                        self.remaining_len -= 1;
                        return Some((key, value));
                    }
                },
                BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
                    let bucket = unsafe { (& *bucket_rc_cell.get()) };
                    let mut iter = bucket.items.iter();
                    let next = iter.next();
                    mem::replace(&mut self.bucket_iter, Some(iter)); 
                    if let Some(&(ref key, ref value)) = next {
                        self.remaining_len -= 1;
                        return Some((key, value));
                    }
                },
                BurstTrieNode::Access(ref access) => {
                    // add to stack in reverse order
                    for i in (1..ALPHABET_SIZE + 1) {
                        let idx = ALPHABET_SIZE - i;
                        let node = &access.nodes[idx];
                        match *node {
                            BurstTrieNode::Bucket(_) |
                            BurstTrieNode::Access(_) => {
                                self.stack.push(node);
                            },
                            BurstTrieNode::Hybrid(_) => {
                                if self.stack.last().map_or(true, |&n| n != node) {
                                    self.stack.push(node);
                                }
                            },
                            _ => unreachable!()
                        }
                    }

                    if let Some((ref key, ref value)) = access.terminator {
                        self.remaining_len -= 1;
                        return Some((key, value));
                    }
                },
                _ => unreachable!()
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining_len, Some(self.remaining_len))
    }
}

pub struct IntoIter<K, V> where K: AsRef<str> {
    stack: Vec<BurstTrieNode<K, V>>,
    bucket_iter: Option<vec::IntoIter<(K, V)>>,
    remaining_len: usize
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> where K: AsRef<str> {}

impl<K, V> Iterator for IntoIter<K, V> where K: AsRef<str> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        if let Some(ref mut iter) = self.bucket_iter {
            let next = iter.next();
            if next.is_some() {
                self.remaining_len -= 1;
                return next;
            }
        }

        while let Some(node) = self.stack.pop() {
            match node {
                BurstTrieNode::Bucket(bucket) => {
                    let mut iter = bucket.items.into_iter();
                    let next = iter.next();
                    mem::replace(&mut self.bucket_iter, Some(iter));
                    if next.is_some() {
                        self.remaining_len -= 1;
                        return next;
                    }
                },
                BurstTrieNode::Hybrid(bucket_rc_cell) => {
                    // let bucket = unsafe { rc::try_unwrap(bucket_rc_cell).ok().unwrap().into_inner() };
                    let bucket = unsafe { mem::replace(&mut *bucket_rc_cell.get(), BucketNode::new()) };
                    let mut iter = bucket.items.into_iter();
                    let next = iter.next();
                    mem::replace(&mut self.bucket_iter, Some(iter));
                    if next.is_some() {
                        self.remaining_len -= 1;
                        return next;
                    }
                },
                BurstTrieNode::Access(mut access) => {
                    // add to stack in reverse order
                    for i in (1..ALPHABET_SIZE + 1) {
                        let idx = ALPHABET_SIZE - i;
                        let node = mem::replace(&mut access.nodes[idx], BurstTrieNode::Empty);
                        match node {
                            BurstTrieNode::Bucket(_) |
                            BurstTrieNode::Access(_) => {
                                self.stack.push(node);
                            },
                            BurstTrieNode::Hybrid(_) => {
                                if self.stack.last().map_or(true, |n| n != &node) {
                                    self.stack.push(node);
                                }
                            },
                            _ => unreachable!()
                        }
                    }

                    if access.terminator.is_some() {
                        self.remaining_len -= 1;
                        return access.terminator;
                    }
                },
                _ => unreachable!()
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining_len, Some(self.remaining_len))
    }
}

// pub struct Range<'a, K: 'a, V: 'a, Q: 'a> where K: AsRef<str>, Q: AsRef<str> {
//     stack: VecDeque<(&'a BurstTrieNode<K, V>, u16, bool, u16, u16)>,
//     curr_item: Option<(&'a [(K, V)], u16, u16)>,
//     min: Bound<&'a Q>,
//     max: Bound<&'a Q>
// }

// impl<'a, K, V, Q: ?Sized> Range<'a, K, V, Q: ?Sized> where K: AsRef<str>, Q: AsRef<str> {

//     fn new(root: &'a BurstTrieNode<K, V>, min: Bound<&'a Q>, max: Bound<&'a Q>) -> Range<'a, K, V, Q: ?Sized> {
//         let mut range = Range {
//             stack: VecDeque::new(),
//             curr_item: None,
//             min: min,
//             max: max
//         };

//         range.stack.push_back((root, 0, true, 0, ALPHABET_SIZE as u16));
//         range.find_min();
//         range.find_max();

//         range
//     }

//     fn find_min(&mut self) {
//         let (min_key, min_included) = match self.min {
//             Bound::Unbounded => return,
//             Bound::Included(key) => (key, true),
//             Bound::Excluded(key) => (key, false)
//         };

//         while let Some((node, depth, _, _, _)) = self.stack.pop_back() {
//             let depthsz = depth as usize;
//             match *node {
//                 BurstTrieNode::Bucket(ref bucket) => {
//                     let res_bs = bucket.items.binary_search_by(|other| {
//                         other.0.as_ref()[depthsz..].cmp(&min_key.as_ref()[depthsz..])
//                     });
//                     let start_pos = match res_bs {
//                         Ok(pos) if ! min_included => pos + 1,
//                         Ok(pos) | Err(pos) => pos
//                     };
//                     self.stack.push_back((node, depth, false, start_pos as u16, bucket.items.len() as u16));
//                     // can only hit a bucket once
//                     return;
//                 },
//                 BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
//                     let bucket = unsafe { (& *bucket_rc_cell.get()) };
//                     let res_bs = bucket.items.binary_search_by(|other| {
//                         other.0.as_ref()[depthsz..].cmp(&min_key.as_ref()[depthsz..])
//                     });
//                     let start_pos = match res_bs {
//                         Ok(pos) if ! min_included => pos + 1,
//                         Ok(pos) | Err(pos) => pos
//                     };
//                     self.stack.push_back((node, depth, false, start_pos as u16, bucket.items.len() as u16));
//                     // can only hit a bucket once
//                     return;
//                 },
//                 BurstTrieNode::Access(ref access) => {
//                     if depthsz < min_key.as_ref().len() {
//                         let mut min_key_byte = min_key.as_ref().as_bytes()[depthsz] as usize;
//                         while min_key_byte + 1 < ALPHABET_SIZE && access.nodes[min_key_byte] == access.nodes[min_key_byte + 1] {
//                             min_key_byte += 1;
//                         }
//                         self.stack.push_back((node, depth, false, min_key_byte as u16 + 1, ALPHABET_SIZE as u16));
//                         match access.nodes[min_key_byte] {
//                             BurstTrieNode::Bucket(ref bucket) =>
//                                self.stack.push_back((&access.nodes[min_key_byte], depth + 1, false, 0, bucket.items.len() as u16)),
//                             BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
//                                 if self.stack.back().map_or(true, |n| n.0 != &access.nodes[min_key_byte]) {   
//                                     self.stack.push_back((&access.nodes[min_key_byte], depth, false, 0, unsafe { (& *bucket_rc_cell.get()).items.len() as u16 }));
//                                 }
//                             },
//                             BurstTrieNode::Access(_) => 
//                                 self.stack.push_back((&access.nodes[min_key_byte], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                             _ => unreachable!() // exit
//                         }
//                     } else {   
//                         // re-add node to the stack with correct terminator and exit
//                         self.stack.push_back((node, depth, min_included, 0, ALPHABET_SIZE as u16));
//                         return;
//                     }
//                 },
//                 _ => unreachable!()
//             }
//         }
//     }

//     fn find_max(&mut self) {
//         let (max_key, max_included) = match self.max {
//             Bound::Unbounded => return,
//             Bound::Included(key) => (key, true),
//             Bound::Excluded(key) => (key, false)
//         };

//         while let Some((node, depth, terminator, start_pos, _)) = self.stack.pop_front() {
//             let depthsz = depth as usize;
//             match *node {
//                 BurstTrieNode::Bucket(ref bucket) => {
//                     let res_bs = bucket.items.binary_search_by(|other| {
//                         other.0.as_ref()[depthsz..].cmp(&max_key.as_ref()[depthsz..])
//                     });
//                     let end_pos = match res_bs {
//                         Ok(pos) if max_included => pos + 1,
//                         Ok(pos) | Err(pos) => pos
//                     };
//                     self.stack.push_front((node, depth, false, start_pos, end_pos as u16));
//                     // can only hit a bucket once
//                     return;
//                 },
//                 BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
//                     let bucket = unsafe { (& *bucket_rc_cell.get()) };
//                     let res_bs = bucket.items.binary_search_by(|other| {
//                         other.0.as_ref()[depthsz..].cmp(&max_key.as_ref()[depthsz..])
//                     });
//                     let end_pos = match res_bs {
//                         Ok(pos) if max_included => pos + 1,
//                         Ok(pos) | Err(pos) => pos
//                     };
//                     self.stack.push_front((node, depth, false, start_pos, end_pos as u16));
//                     // can only hit a bucket once
//                     return;
//                 },
//                 BurstTrieNode::Access(ref access) => {
//                     if depthsz < max_key.as_ref().len() {
//                         let mut max_key_byte = max_key.as_ref().as_bytes()[depthsz] as usize;
//                         self.stack.push_front((node, depth, terminator, start_pos, max_key_byte as u16));
//                         while max_key_byte > 0 && access.nodes[max_key_byte] == access.nodes[max_key_byte - 1] {
//                             max_key_byte -= 1;
//                         }
//                         match access.nodes[max_key_byte] {
//                             BurstTrieNode::Bucket(ref bucket) => {
//                                 self.stack.push_front((&access.nodes[max_key_byte], depth + 1, false, 0, bucket.items.len() as u16))
//                             },
//                             BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
//                                 if self.stack.front().map_or(true, |n| n.0 != &access.nodes[max_key_byte]) {
//                                     self.stack.push_front((&access.nodes[max_key_byte], depth, false, 0, unsafe { (& *bucket_rc_cell.get()).items.len() as u16 }));
//                                 }
//                             },
//                             BurstTrieNode::Access(_) => {

//                                 self.stack.push_front((&access.nodes[max_key_byte], depth + 1, true, 0, ALPHABET_SIZE as u16))
//                             },
//                             _ => unreachable!()
//                         }
//                     } else {
//                         // re-add node to the stack with correct terminator and exit
//                         self.stack.push_front((node, depth, max_included, 0, 0));
//                         return;
//                     }
//                 },
//                 _ => unreachable!()
//             }
//         }
//     }

//     fn find_next(&mut self) -> Option<(&'a K, &'a V)> {
//         if let Some((items, ref mut start_pos, end_pos)) = self.curr_item {
//             if *start_pos < end_pos {
//                 let (ref key, ref value) = items[*start_pos as usize];
//                 *start_pos += 1; // advance iterator
//                 return Some((key, value));
//             }
//         }

//         while let Some((node, depth, terminator, start_pos, end_pos)) = self.stack.pop_back() {
//             match *node {
//                 BurstTrieNode::Bucket(ref bucket) => {
//                     if start_pos < end_pos {
//                         self.curr_item = Some((&bucket.items[..], start_pos + 1, end_pos));
//                         let (ref key, ref value) = bucket.items[start_pos as usize];
//                         return Some((key, value));
//                     }
//                 },
//                 BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
//                     if start_pos < end_pos {
//                         let bucket = unsafe { (& *bucket_rc_cell.get()) };
//                         self.curr_item = Some((&bucket.items[..], start_pos + 1, end_pos));
//                         let (ref key, ref value) = bucket.items[start_pos as usize];
//                         return Some((key, value));
//                     }
//                 },
//                 BurstTrieNode::Access(ref access) => {
//                     // add to stack in reverse order
//                     for i in ((ALPHABET_SIZE - end_pos as usize) + 1 .. (ALPHABET_SIZE - start_pos as usize) + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         match access.nodes[idx] {
//                             BurstTrieNode::Bucket(ref bucket) => {
//                                 self.stack.push_back((&access.nodes[idx], depth + 1, false, 0, bucket.items.len() as u16));
//                             },
//                             BurstTrieNode::Hybrid(ref bucket_rc_cell) => {
//                                 if self.stack.back().map_or(true, |n| n.0 != &access.nodes[idx]) {
//                                     self.stack.push_back((&access.nodes[idx], depth, false, 0, unsafe { (& *bucket_rc_cell.get()).items.len() as u16 }));
//                                 }
//                             },
//                             BurstTrieNode::Access(_) => {
//                                 self.stack.push_back((&access.nodes[idx], depth + 1, true, 0, ALPHABET_SIZE as u16));
//                             },
//                             _ => unreachable!()
//                         }
//                     }

//                     if terminator {
//                         if let Some((ref key, ref value)) = access.terminator {
//                             return Some((key, value));
//                         }
//                     }
//                 },
//                 _ => unreachable!()
//             }
//         }

//         None
//     }
// }

// impl<'a, K, V, Q: ?Sized> Iterator for Range<'a, K, V, Q: ?Sized> where K: AsRef<str>, Q: AsRef<str> {
//     type Item = (&'a K, &'a V);

//     #[inline(always)]
//     fn next(&mut self) -> Option<(&'a K, &'a V)> {
//         self.find_next()
//     }

//     #[inline(always)]
//     fn size_hint(&self) -> (usize, Option<usize>) {
//         (self.stack.len(), None)
//     }
// }

#[cfg(test)]
mod tests {
    use super::BurstTrieMap;
    // use collections::Bound;
    use rand::*;

    #[test]
    fn test_iter() {
        let mut map = BurstTrieMap::new();

        for i in (100000..999999) {
            map.insert(i.to_string(), i);
        }

        let mut i = 100000usize;
        for (key, value) in map.iter() {
            assert_eq!(key.parse::<usize>().unwrap(), i);
            assert_eq!(*value, i);
            i += 1;
        }
        assert_eq!(i, 999999);
    }

    // #[test]
    // fn test_range1() {
    //     let mut map = BurstTrieMap::new();

    //     for i in (100000..999999) {
    //         map.insert(i.to_string(), i);
    //     }

    //     let mut i = 100000usize;
    //     for (key, value) in map.range::<String>(Bound::Unbounded, Bound::Unbounded) {
    //         assert_eq!(key.parse::<usize>().unwrap(), i);
    //         assert_eq!(*value, i);
    //         i += 1;
    //     }
    //     assert_eq!(i, 999999);

    //     for j in (999000..999999) {
    //         let mut i = j;
    //         for (key, value) in map.range(Bound::Included(&j.to_string()), Bound::Unbounded) {
    //             assert_eq!(key.parse::<usize>().unwrap(), i);
    //             assert_eq!(*value, i);
    //             i += 1;
    //         }
    //         assert_eq!(i, 999999);
    //     }

    //     for j in (999000..999999) {
    //         let mut i = j + 1;
    //         for (key, value) in map.range(Bound::Excluded(&j.to_string()), Bound::Unbounded) {
    //             assert_eq!(key.parse::<usize>().unwrap(), i);
    //             assert_eq!(*value, i);
    //             i += 1;
    //         }
    //         assert_eq!(i, 999999);
    //     }

    //     assert_eq!(map.range(Bound::Included("999998"), Bound::Unbounded).count(), 1);
    //     assert_eq!(map.range(Bound::Excluded("999998"), Bound::Unbounded).count(), 0);
    //     assert_eq!(map.range(Bound::Excluded("999999"), Bound::Unbounded).count(), 0);

    //     // 2 items that will be at the terminator slots
    //     map.insert("1".to_string(), 1);
    //     map.insert("2".to_string(), 2);
    //     assert_eq!(map.range(Bound::Included("1"), Bound::Unbounded).count(), (999999 - 100000) + 2);
    //     assert_eq!(map.range(Bound::Excluded("1"), Bound::Unbounded).count(), (999999 - 100000) + 1);
    //     assert_eq!(map.range(Bound::Included("2"), Bound::Unbounded).count(), (999999 - 100000) + 1 - 100000);
    //     assert_eq!(map.range(Bound::Excluded("2"), Bound::Unbounded).count(), (999999 - 100000) - 100000);

    //     // max specified
    //     assert_eq!(map.range(Bound::Excluded("1"), Bound::Excluded("2")).count(), 100000);
    //     assert_eq!(map.range(Bound::Excluded("2"), Bound::Excluded("3")).count(), 100000);
    //     assert_eq!(map.range(Bound::Included("1"), Bound::Included("2")).count(), 100000 + 2);
    //     assert_eq!(map.range(Bound::Included("2"), Bound::Included("3")).count(), 100000 + 1);
    // }

    // #[test]
    // fn test_range2() {
    //     use rand::{Rng, weak_rng};
    //     use std::collections::{BTreeMap, Bound};

    //     let mut rng = weak_rng();
    //     let mut tree = BTreeMap::new();
    //     let mut trie = BurstTrieMap::new();
    //     let value = 0usize;

    //     (0..10000).map(|_| {
    //         let key_len = rng.gen_range(0, 100);
    //         let key = rng.gen_ascii_chars().take(key_len).collect::<String>();
    //         tree.insert(key.clone(), value);
    //         trie.insert(key, value);
    //     }).count();

    //     let keys = tree.keys().collect::<Vec<_>>();
    //     assert_eq!(keys, trie.keys().collect::<Vec<_>>());

    //     for i in (0..1000) {
    //         let x0 = rng.gen_range(0usize, keys.len());
    //         let x1 = rng.gen_range(x0, keys.len());
    //         let min1 = Bound::Included(keys[x0]);
    //         let max1 = Bound::Excluded(keys[x1]);
    //         let min2 = Bound::Included(keys[x0]);
    //         let max2 = Bound::Excluded(keys[x1]);
    //         for ((key1, _), (key2, _)) in tree.range(min1, max1).zip(trie.range(min2, max2)) {
    //             assert_eq!(key1, key2);
    //         }
    //     }
    // }

    #[test]
    fn test_into_iter() {
        let mut map = BurstTrieMap::new();

        // use a dropable value so it crashes if double drop
        for i in (100000..999999) {
            map.insert(i.to_string(), i.to_string());
        }

        let mut i = 100000usize;
        for (key, value) in map.into_iter() {
            assert_eq!(key.parse::<usize>().unwrap(), i);
            assert_eq!(value.parse::<usize>().unwrap(), i);
            i += 1;
        }
        assert_eq!(i, 999999);
    }

    #[test]
    fn test_keys() {
        let mut map = BurstTrieMap::new();

        for i in (100000..999999) {
            map.insert(i.to_string(), i);
        }

        let mut i = 100000usize;
        for key in map.keys() {
            assert_eq!(key.parse::<usize>().unwrap(), i);
            i += 1;
        }
        assert_eq!(i, 999999);
    }

    #[test]
    fn test_values() {
        let mut map = BurstTrieMap::new();

        for i in (100000..999999) {
            map.insert(i.to_string(), i);
        }

        let mut i = 100000usize;
        for value in map.values() {
            assert_eq!(*value, i);
            i += 1;
        }
        assert_eq!(i, 999999);
    }

    #[test]
    fn test_correctness() {
        let mut rng = weak_rng();
        for _ in (0..10) {
            let mut trie = BurstTrieMap::new();
            for _ in (0..10000) {
                let key_len = rng.gen_range(1usize, 1000);
                let key = rng.gen_ascii_chars().take(key_len).collect::<String>();
                let value = rng.gen::<usize>();
                trie.insert(key.clone(), value);
                if let Some(r_value) = trie.get(&key) {
                    assert_eq!(value, *r_value);
                } else {
                    panic!("key: {} not found", key);
                }
            }
        }
    }

    #[test]
    fn find_empty() {
        let m: BurstTrieMap<String,i32> = BurstTrieMap::new();
        assert!(m.get("5") == None);
    }

    #[test]
    fn find_not_found() {
        let mut m = BurstTrieMap::new();
        assert!(m.insert("1", 2).is_none());
        assert!(m.insert("5", 3).is_none());
        assert!(m.insert("9", 3).is_none());
        assert_eq!(m.get("2"), None);
    }

    #[test]
    fn test_len() {
        let mut m = BurstTrieMap::new();
        assert!(m.insert("3", 6).is_none());
        assert_eq!(m.len(), 1);
        assert!(m.insert("0", 0).is_none());
        assert_eq!(m.len(), 2);
        assert!(m.insert("4", 8).is_none());
        assert_eq!(m.len(), 3);
        assert!(m.remove("3").is_some());
        assert_eq!(m.len(), 2);
        assert!(!m.remove("5").is_some());
        assert_eq!(m.len(), 2);
        assert!(m.insert("2", 4).is_none());
        assert_eq!(m.len(), 3);
        assert!(m.insert("1", 2).is_none());
        assert_eq!(m.len(), 4);
    }

    #[test]
    fn insert_replace() {
        let mut m = BurstTrieMap::new();
        assert!(m.insert("5", 2).is_none());
        assert!(m.insert("2", 9).is_none());
        assert!(!m.insert("2", 11).is_none());
        assert_eq!(m.get("2").unwrap(), &11);
    }

    #[test]
    fn test_swap() {
        let mut m = BurstTrieMap::new();
        assert_eq!(m.insert("1", 2), None);
        assert_eq!(m.insert("1", 3), Some(2));
        assert_eq!(m.insert("1", 4), Some(3));
    }

    #[test]
    fn test_pop() {
        let mut m = BurstTrieMap::new();
        m.insert("1", 2);
        assert_eq!(m.remove("1"), Some(2));
        assert_eq!(m.remove("1"), None);
    }

    #[test]
    fn test_clear() {
        let mut m = BurstTrieMap::new();
        m.clear();
        assert!(m.insert("5", 11).is_none());
        assert!(m.insert("2", -3).is_none());
        assert!(m.insert("9", 2).is_none());
        m.clear();
        assert!(m.get("5").is_none());
        assert!(m.get("2").is_none());
        assert!(m.get("9").is_none());
        assert!(m.is_empty());
    }

    #[test]
    fn test_index() {
        let mut m = BurstTrieMap::new();
        m.insert("1", 2);
        assert_eq!(m["1"], 2);
        {
            let ref_1 = &mut m["1"];
            *ref_1 = 3;
        }
        assert_eq!(m["1"], 3);
    }
}


#[cfg(test)]
mod bench {
    use test;
    use super::BurstTrieMap;
    use bench_macros::BENCH_SEED;

    map_get_rnd_bench!(burst_get_short_1000, 5, 15, 1000, BurstTrieMap);
    map_get_rnd_bench!(burst_get_short_10000, 5, 15, 10000, BurstTrieMap);
    map_get_rnd_bench!(burst_get_short_100000, 5, 15, 100000, BurstTrieMap);
    map_get_rnd_bench!(burst_get_medium_1000, 20, 100, 1000, BurstTrieMap);
    map_get_rnd_bench!(burst_get_medium_10000, 20, 100, 10000, BurstTrieMap);
    map_get_rnd_bench!(burst_get_medium_100000, 20, 100, 100000, BurstTrieMap);
    map_insert_rnd_bench!(burst_insert_short_1000, 5, 15, 1000, BurstTrieMap);
    map_insert_rnd_bench!(burst_insert_short_10000, 5, 15, 10000, BurstTrieMap);
    map_insert_rnd_bench!(burst_insert_short_100000, 5, 15, 100000, BurstTrieMap);
    map_insert_rnd_bench!(burst_insert_medium_1000, 20, 100, 1000, BurstTrieMap);
    map_insert_rnd_bench!(burst_insert_medium_10000, 20, 100, 10000, BurstTrieMap);
    map_insert_rnd_bench!(burst_insert_medium_100000, 20, 100, 100000, BurstTrieMap);

    map_get_rnd_bench!(burst_get_prefix_medium_10000, 20, 100, 10000, BurstTrieMap, "https://www.");
    map_get_rnd_bench!(burst_get_prefix_medium_100000, 20, 100, 100000, BurstTrieMap, "https://www.");
    map_insert_rnd_bench!(burst_insert_prefix_medium_10000, 20, 100, 10000, BurstTrieMap, "https://www.");
    map_insert_rnd_bench!(burst_insert_prefix_medium_100000, 20, 100, 100000, BurstTrieMap, "https://www.");


    map_get_seq_bench!(burst_get_seq_100000, 20, 100, 100000, BurstTrieMap);
    map_insert_seq_bench!(burst_insert_seq_100000, 20, 100, 100000, BurstTrieMap);

    map_iter_bench!(burst_iter_10000, 20, 100, 10000, BurstTrieMap);
    // map_range_bench!(burst_range_10000, 20, 100, 10000, BurstTrieMap);



    use std::collections::BTreeMap;
    map_get_rnd_bench!(btree_get_short_1000, 5, 15, 1000, BTreeMap);
    map_get_rnd_bench!(btree_get_short_10000, 5, 15, 10000, BTreeMap);
    map_get_rnd_bench!(btree_get_short_100000, 5, 15, 100000, BTreeMap);
    map_get_rnd_bench!(btree_get_medium_1000, 20, 100, 1000, BTreeMap);
    map_get_rnd_bench!(btree_get_medium_10000, 20, 100, 10000, BTreeMap);
    map_get_rnd_bench!(btree_get_medium_100000, 20, 100, 100000, BTreeMap);
    map_insert_rnd_bench!(btree_insert_short_1000, 5, 15, 1000, BTreeMap);
    map_insert_rnd_bench!(btree_insert_short_10000, 5, 15, 10000, BTreeMap);
    map_insert_rnd_bench!(btree_insert_short_100000, 5, 15, 100000, BTreeMap);
    map_insert_rnd_bench!(btree_insert_medium_1000, 20, 100, 1000, BTreeMap);
    map_insert_rnd_bench!(btree_insert_medium_10000, 20, 100, 10000, BTreeMap);
    map_insert_rnd_bench!(btree_insert_medium_100000, 20, 100, 100000, BTreeMap);

    map_get_rnd_bench!(btree_get_prefix_medium_10000, 20, 100, 10000, BTreeMap, "https://www.");
    map_get_rnd_bench!(btree_get_prefix_medium_100000, 20, 100, 100000, BTreeMap, "https://www.");
    map_insert_rnd_bench!(btree_insert_prefix_medium_10000, 20, 100, 10000, BTreeMap, "https://www.");
    map_insert_rnd_bench!(btree_insert_prefix_medium_100000, 20, 100, 100000, BTreeMap, "https://www.");


    map_get_seq_bench!(btree_get_seq_100000, 20, 100, 100000, BTreeMap);
    map_insert_seq_bench!(btree_insert_seq_100000, 20, 100, 100000, BTreeMap);


    map_iter_bench!(btree_iter_10000, 20, 100, 10000, BTreeMap);
    // map_range_bench!(btree_range_10000, 20, 100, 10000, BTreeMap);
}
