/// Implements an ordered map as a BurstTrie. It's a very fast Trie variant specialized for Str types.
///
/// This structure achieves better performance than a BTree implementations for common operations while
/// still allowing range scanning and ordered iteration. Performance wise it's usually 50+% faster than
/// the std lib BTreeMap for random keys and pulls ahead rapdily if keys have common prefixes.
///
/// It's specialized for string keys, specifically ASCII or UTF-8.
///
/// The Burst Trie was original described by S. Heinz.
/// You can find the original paper in the internet by it's title
/// "Burst Tries: A Fast, Efficient Data Structure for String Keys"

use std::cmp::Ordering;
use std::mem;

const ALPHABET_SIZE: usize = 128; // ascii AND utf-8 compatible
const CONTAINER_SIZE: usize = 64;

/// An BurstTrie implementation of an ordered map. Specialized for Str types.
///
/// See module level docs for details.
pub struct BurstTrieMap<K, V> where K: Str, K: Ord {
    root: BurstTrieNode<K, V>,
    len: usize
}

enum BurstTrieNode<K, V> where K: Str, K: Ord {
    Empty,
    Container(ContainerNode<K, V>),
    Access(AccessNode<K, V>)
}

struct ContainerNode<K, V> where K: Str, K: Ord {
    items: Vec<(K, V)>
}

struct AccessNode<K, V> where K: Str, K: Ord {
    nodes: Box<[BurstTrieNode<K, V>; ALPHABET_SIZE]>,
    terminator: Option<(K, V)>
}

impl<K, V> BurstTrieMap<K, V> where K: Str, K: Ord {
    
    /// Returns a new empty BurstTrieMap
    pub fn new() -> BurstTrieMap<K, V> {
        BurstTrieMap {
            root: BurstTrieNode::Empty,
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
        let opt_old_value = self.root.insert(key, value, 0);
        if opt_old_value.is_none() {
            self.len += 1;
        }
        opt_old_value
    }


    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V> where Q: Str {
        self.root.get(key, 0)
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V> where Q: Str {
        self.root.get_mut(key, 0)
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool where Q: Str {
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
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V> where Q: Str {
        let opt_old_value = self.root.remove(key, 0);
        if opt_old_value.is_some() {
            self.len -= 1;
        }
        opt_old_value
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
        self.root = BurstTrieNode::Empty;
        self.len = 0;
    }
}

impl<K, V> BurstTrieNode<K, V> where K: Str, K: Ord  {

    #[inline]
    fn insert(&mut self, key: K, value: V, depth: usize) -> Option<V> {
        match *self {
            BurstTrieNode::Empty => {
                *self = BurstTrieNode::Container(ContainerNode::from_key_value(key, value));
                return None
            },
            BurstTrieNode::Container(ref mut container) => {
                let result = container.insert(key, value, depth);
                if ! container.need_burst() {
                    return result;
                }
            },
            BurstTrieNode::Access(ref mut access) => {
                return access.insert(key, value, depth)
            },
        }

        // if we reach here the container needs bursting
        self.burst_container(depth);
        None
    }

    #[inline]
    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<V> where Q: Str {
        match *self {
            BurstTrieNode::Empty => {
                None
            },
            BurstTrieNode::Container(ref mut container) => {
                container.remove(key, depth)
            },
            BurstTrieNode::Access(ref mut access) => {
                access.remove(key, depth)
            },
        }
    }

    #[inline]
    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: Str {
        match *self {
            BurstTrieNode::Empty => {
                None
            },
            BurstTrieNode::Container(ref container) => {
                container.get(key, depth)
            },
            BurstTrieNode::Access(ref access) => {
                access.get(key, depth)
            },
        }
    }

    #[inline]
    fn get_mut<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<&mut V> where Q: Str {
        match *self {
            BurstTrieNode::Empty => {
                None
            },
            BurstTrieNode::Container(ref mut container) => {
                container.get_mut(key, depth)
            },
            BurstTrieNode::Access(ref mut access) => {
                access.get_mut(key, depth)
            },
        }
    }

    fn burst_container(&mut self, depth: usize) {
        let old_self = mem::replace(self, BurstTrieNode::Empty);
        if let BurstTrieNode::Container(old_container) = old_self {
            *self = BurstTrieNode::Access(AccessNode::from_container(old_container, depth));
        } else {
            panic!("must be a container!");
        }
    }
}


impl<K, V> ContainerNode<K, V> where K: Str, K: Ord {
    fn from_key_value(key: K, value: V) -> ContainerNode<K, V> {
        let mut container = ContainerNode {
            items: Vec::with_capacity(CONTAINER_SIZE)
        };
        container.items.push((key, value));

        container
    }

    #[inline]
    fn insert(&mut self, key: K, value: V, depth: usize) -> Option<V> {
        // optimize insertions at the end
        // helps in seq insert and node bursting
        let seq_insert = match self.items.last_mut() {
            Some(&mut (ref last_key, ref mut last_value)) =>
                match last_key.as_slice()[depth..].cmp(&key.as_slice()[depth..]) {
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
            let res_bs = self.items.init().binary_search_by(|other| {
                other.0.as_slice()[depth..].cmp(&key.as_slice()[depth..])
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
    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<V> where Q: Str {
        let res_bs = self.items.binary_search_by(|other| {
            other.0.as_slice()[depth..].cmp(&key.as_slice()[depth..])
        });
        match res_bs {
            Ok(pos) => Some(self.items.remove(pos).1),
            Err(pos) => None
        }
    }

    #[inline]
    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: Str {
        // FIXME: binary search is doing bounds checking internally ;/ 
        let res_bs = self.items.binary_search_by(|other| {
            other.0.as_slice()[depth..].cmp(&key.as_slice()[depth..])
        });
        if let Ok(pos) = res_bs {
            Some(unsafe { &self.items.get_unchecked(pos).1 })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<&mut V> where Q: Str {
        // FIXME: binary search is doing bounds checking internally ;/ 
        let res_bs = self.items.binary_search_by(|other| {
            other.0.as_slice()[depth..].cmp(&key.as_slice()[depth..])
        });
        if let Ok(pos) = res_bs {
            Some(unsafe { &mut self.items.get_unchecked_mut(pos).1 })
        } else {
            None
        }
    }

    #[inline]
    fn need_burst(&self) -> bool {
        self.items.len() > CONTAINER_SIZE
    }
}

impl<K, V> AccessNode<K, V> where K: Str, K: Ord {
    fn from_container(container: ContainerNode<K, V>, depth: usize) -> AccessNode<K, V> {
        let mut access_node = AccessNode {
            nodes: Box::new(unsafe { mem::zeroed() }),
            terminator: None
        };
        for (key, value) in container.items {
            access_node.insert(key, value, depth);
        }
        access_node
    }

    #[inline]
    fn insert(&mut self, key: K, value: V, depth: usize) -> Option<V> {
        // depth is always <= key.len
        if depth < key.as_slice().len() {
            let idx = key.as_slice().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            self.nodes[idx].insert(key, value, depth + 1)
        } else if let Some((_, ref mut old_value)) = self.terminator {
            Some(mem::replace(old_value, value))
        } else {
            self.terminator = Some((key, value));
            None
        }
    }


    #[inline]
    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<V> where Q: Str {
        if depth < key.as_slice().len() {
            let idx = key.as_slice().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            self.nodes[idx].remove(key, depth + 1)
        } else if let Some((_, old_value)) = self.terminator.take() {
            Some(old_value)
        } else {
            None
        }
    }

    #[inline]
    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: Str {
        if depth < key.as_slice().len() {
            let idx = key.as_slice().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            self.nodes[idx].get(key, depth + 1)
        } else {
            if let Some((_, ref v)) = self.terminator {
                Some(v)
            } else {
                None
            }
        }
    }

    #[inline]
    fn get_mut<Q: ?Sized>(&mut self, key: &Q, depth: usize) -> Option<&mut V> where Q: Str {
        if depth < key.as_slice().len() {
            let idx = key.as_slice().as_bytes()[depth] as usize;
            debug_assert!(idx < ALPHABET_SIZE);
            self.nodes[idx].get_mut(key, depth + 1)
        } else {
            if let Some((_, ref mut v)) = self.terminator {
                Some(v)
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use test;
    use super::BurstTrieMap;
    use rand::*;

    #[test]
    fn test_correctness() {
        let mut rng = weak_rng();
        for _ in (0..5) {
            let mut trie = BurstTrieMap::new();
            for _ in (0..1000) {
                let key = rng.gen_ascii_chars().take(thread_rng().gen_range(1usize, 1000)).collect::<String>();
                let value = rng.gen::<usize>();
                trie.insert(key.clone(), value);
                if let Some(r_value) = trie.get(&key) {
                    assert_eq!(value, *r_value);
                } else {
                    assert!(false);
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

    map_get_seq_bench!(burst_get_seq_100000, 20, 100, 100000, BurstTrieMap);
    map_insert_seq_bench!(burst_insert_seq_100000, 20, 100, 100000, BurstTrieMap);


    map_get_rnd_bench!(burst_get_prefix_medium_10000, 20, 100, 10000, BurstTrieMap, "https://www.");
    map_get_rnd_bench!(burst_get_prefix_medium_100000, 20, 100, 100000, BurstTrieMap, "https://www.");
    map_insert_rnd_bench!(burst_insert_prefix_medium_10000, 20, 100, 10000, BurstTrieMap, "https://www.");
    map_insert_rnd_bench!(burst_insert_prefix_medium_100000, 20, 100, 100000, BurstTrieMap, "https://www.");


    // use std::collections::BTreeMap;
    // map_get_rnd_bench!(btree_get_short_1000, 5, 15, 1000, BTreeMap);
    // map_get_rnd_bench!(btree_get_short_10000, 5, 15, 10000, BTreeMap);
    // map_get_rnd_bench!(btree_get_short_100000, 5, 15, 100000, BTreeMap);
    // map_get_rnd_bench!(btree_get_medium_1000, 20, 100, 1000, BTreeMap);
    // map_get_rnd_bench!(btree_get_medium_10000, 20, 100, 10000, BTreeMap);
    // map_get_rnd_bench!(btree_get_medium_100000, 20, 100, 100000, BTreeMap);
    // map_insert_rnd_bench!(btree_insert_short_1000, 5, 15, 1000, BTreeMap);
    // map_insert_rnd_bench!(btree_insert_short_10000, 5, 15, 10000, BTreeMap);
    // map_insert_rnd_bench!(btree_insert_short_100000, 5, 15, 100000, BTreeMap);
    // map_insert_rnd_bench!(btree_insert_medium_1000, 20, 100, 1000, BTreeMap);
    // map_insert_rnd_bench!(btree_insert_medium_10000, 20, 100, 10000, BTreeMap);
    // map_insert_rnd_bench!(btree_insert_medium_100000, 20, 100, 100000, BTreeMap);

    // map_get_rnd_bench!(btree_get_prefix_medium_10000, 20, 100, 10000, BTreeMap, "https://www.");
    // map_get_rnd_bench!(btree_get_prefix_medium_100000, 20, 100, 100000, BTreeMap, "https://www.");
    // map_insert_rnd_bench!(btree_insert_prefix_medium_10000, 20, 100, 10000, BTreeMap, "https://www.");
    // map_insert_rnd_bench!(btree_insert_prefix_medium_100000, 20, 100, 100000, BTreeMap, "https://www.");


    // map_get_seq_bench!(btree_get_seq_100000, 20, 100, 100000, BTreeMap);
    // map_insert_seq_bench!(btree_insert_seq_100000, 20, 100, 100000, BTreeMap);
}