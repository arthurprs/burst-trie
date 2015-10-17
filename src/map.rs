/// Implements an ordered map as an Adaptive BurstTrie.
///
/// This structure achieves better performance than a BTree implementations for common operations while
/// still allowing range scanning and ordered iteration. Performance wise it's usually 50+% faster than
/// the std lib BTreeMap for random keys and pulls ahead further if keys have common prefixes.
///
/// It's specialized for byte ordered keys, like ASCII or UTF-8 strings.
///
/// The Burst Trie was originaly described by S. Heinz.
/// You can find the original paper in the internet by it's title
/// "Burst Tries: A Fast, Efficient Data Structure for String Keys"

use std::ptr;
use std::mem;
use std::slice;
use std::vec;
use std::collections::Bound;
use std::cmp::{self, Ordering};
use std::default::Default;
use std::ops::{Index, IndexMut};
use std::collections::VecDeque;
use std::iter::Map;
use std::marker;
use std::fmt;

const ALPHABET_SIZE: usize = 256;
const CONTAINER_SIZE: usize = 32;
const SMALL_ACCESS_SIZE: usize = 64;

/// An BurstTrie implementation of an ordered map. Specialized for byte ordered types.
///
/// See module level docs for details.
pub struct BurstTrieMap<K, V> where K: AsRef<[u8]> {
    root: *mut BurstTrieNode<K, V>,
    len: usize
}

#[derive(Copy, Clone, Debug)]
#[repr(u8)]
enum BurstTrieNodeType {
    Empty,
    Container,
    Access,
    SmallAccess,
}

#[repr(C)]
struct BurstTrieNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    marker: marker::PhantomData<(K, V)>,
}

#[repr(C)]
struct ContainerNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    items: Vec<(K, V)>
}

#[repr(C)]
struct AccessNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    nodes: [*mut BurstTrieNode<K, V>; ALPHABET_SIZE],
    terminator: Option<(K, V)>
}

#[repr(C)]
struct SmallAccessNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    len: u8,
    index: [u8; ALPHABET_SIZE],
    snodes: [*mut BurstTrieNode<K, V>; SMALL_ACCESS_SIZE],
    terminator: Option<(K, V)>
}

impl<K, V> BurstTrieMap<K, V> where K: AsRef<[u8]> {
    
    /// Returns a new empty BurstTrieMap
    pub fn new() -> BurstTrieMap<K, V> {
        BurstTrieMap {
            root: ptr::null_mut(),
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
        let opt_old_value = BurstTrieNode::insert(self.root, key, value, 0, &mut self.root);
        if opt_old_value.is_none() {
            self.len += 1;
        }
        opt_old_value
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
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V> where Q: AsRef<[u8]> {
        BurstTrieNode::get(self.root, key, 0)
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
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V> where Q: AsRef<[u8]> {
        unsafe { mem::transmute(self.get(key)) }
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
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool where Q: AsRef<[u8]> {
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
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V> where Q: AsRef<[u8]> {
        let opt_old_value = BurstTrieNode::remove(self.root, key, 0, &mut self.root);
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
        BurstTrieNode::drop(self.root);
        self.root = ptr::null_mut();
        self.len = 0;
    }

    pub fn print_structure(&self) {
        BurstTrieNode::print_structure(self.root, 0);
    }

    // pub fn iter(&self) -> Iter<K, V> {
    //     Iter {
    //         stack: vec![&self.root],
    //         container_iter: None,
    //         remaining_len: self.len
    //     }
    // }
    
    // pub fn into_iter(self) -> IntoIter<K, V> {
    //     IntoIter {
    //         stack: vec![self.root],
    //         container_iter: None,
    //         remaining_len: self.len
    //     }
    // }

    // pub fn keys<'a>(&'a self) -> Map<Iter<K, V>, fn((&'a K, &'a V)) -> &'a K> {
    //     #[inline(always)]
    //     fn map_fn<'a, K, V>(kv: (&'a K, &'a V)) -> &'a K {
    //         &kv.0
    //     }
    //     self.iter().map(map_fn)
    // }

    // pub fn values<'a>(&'a self) -> Map<Iter<K, V>, fn((&'a K, &'a V)) -> &'a V> {
    //     #[inline(always)]
    //     fn map_fn<'a, K, V>(kv: (&'a K, &'a V)) -> &'a V {
    //         &kv.1
    //     }
    //     self.iter().map(map_fn)
    // }

    // pub fn range<'a, Q: ?Sized>(&'a self, min: Bound<&'a Q>, max: Bound<&'a Q>) -> Range<K, V, Q> where Q: AsRef<[u8]> {
    //     Range::new(&self.root, min, max)
    // }
}

impl<K, V> Drop for BurstTrieMap<K, V> where K: AsRef<[u8]> {
    fn drop(&mut self) {
        BurstTrieNode::drop(self.root);
    }
}

type BurstTrieNodeRef<K, V> = *mut *mut BurstTrieNode<K, V>;

impl<K, V> BurstTrieNode<K, V> where K: AsRef<[u8]>  {
    #[inline]
    fn _type(n: *const Self) -> BurstTrieNodeType {
        if n.is_null() {
            BurstTrieNodeType::Empty
        } else {
            unsafe { (*n)._type }
        }
    }

    #[inline]
    fn as_container<'a>(n: *const Self) -> &'a mut ContainerNode<K, V> {
        unsafe { mem::transmute(n) }
    }

    #[inline]
    fn as_small_access<'a>(n: *const Self) -> &'a mut SmallAccessNode<K, V> {
        unsafe { mem::transmute(n) }
    }

    #[inline]
    fn as_access<'a>(n: *const Self) -> &'a mut AccessNode<K, V> {
        unsafe { mem::transmute(n) }
    }

    #[inline]
    fn insert(n: *mut Self, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> {
        match BurstTrieNode::_type(n) {
            BurstTrieNodeType::Empty => {
                unsafe {
                    *node_ref = Box::into_raw(ContainerNode::from_key_value(key, value)) as *mut _;
                }
                None
            },
            BurstTrieNodeType::Container => {
                BurstTrieNode::as_container(n).insert(key, value, depth, node_ref)
            },
            BurstTrieNodeType::Access => {
                BurstTrieNode::as_access(n).insert(key, value, depth, node_ref)
            },
            BurstTrieNodeType::SmallAccess => {
                BurstTrieNode::as_small_access(n).insert(key, value, depth, node_ref)
            },
        }
    }

    #[inline]
    fn remove<Q: ?Sized>(n: *mut Self, key: &Q, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V>
    where Q: AsRef<[u8]> {
        // FIXME: we probably want to do some node colapsing here or in a shrink_to_fit method
        match BurstTrieNode::_type(n) {
            BurstTrieNodeType::Empty => {
                None
            },
            BurstTrieNodeType::Container => {
                BurstTrieNode::as_container(n).remove(key, depth, node_ref)
            },
            BurstTrieNodeType::Access => {
                BurstTrieNode::as_access(n).remove(key, depth, node_ref)
            },
            BurstTrieNodeType::SmallAccess => {
                BurstTrieNode::as_small_access(n).remove(key, depth, node_ref)
            },
        }
    }

    #[inline]
    fn get<'a, Q:?Sized>(n: *mut Self, key: &Q, depth: usize) -> Option<&'a V>
    where Q: AsRef<[u8]>, K: 'a {
        match BurstTrieNode::_type(n) {
            BurstTrieNodeType::Empty => {
                None
            },
            BurstTrieNodeType::Container => {
                BurstTrieNode::as_container(n).get(key, depth)
            },
            BurstTrieNodeType::Access => {
                BurstTrieNode::as_access(n).get(key, depth)
            },
            BurstTrieNodeType::SmallAccess => {
                BurstTrieNode::as_small_access(n).get(key, depth)
            },
        }
    }

    #[inline]
    fn drop(n: *mut Self) {
        unsafe {
            match BurstTrieNode::_type(n) {
                BurstTrieNodeType::Container => {
                    drop(Box::from_raw(n as *mut ContainerNode<K, V>))
                },
                BurstTrieNodeType::Access => {
                    drop(Box::from_raw(n as *mut AccessNode<K, V>))
                },
                BurstTrieNodeType::SmallAccess => {
                    drop(Box::from_raw(n as *mut SmallAccessNode<K, V>))
                },
                BurstTrieNodeType::Empty => ()
            }
        }
    }

    #[inline]
    fn print_structure(n: *mut Self, mut depth: usize) {
        match BurstTrieNode::_type(n) {
            BurstTrieNodeType::Container => {
                println!("{}Container(LEN {})",
                    (0..depth).map(|_| ' ').collect::<String>(),
                    Self::as_container(n).items.len());
            },
            BurstTrieNodeType::Access => {
                let access = Self::as_access(n);
                for (c, &node) in access.nodes.iter().enumerate() {
                    println!("{}Access({})",
                        (0..depth).map(|_| ' ').collect::<String>(),
                        c as u8 as char);
                    Self::print_structure(node, depth + 1);
                }
            },
            BurstTrieNodeType::SmallAccess => {
                let small_access = Self::as_small_access(n);
                println!("{}SmallAccess(LEN {})",
                    (0..depth).map(|_| ' ').collect::<String>(),
                    small_access.len);
                depth += 1;
                for (c, &i) in small_access.index.iter().enumerate() {
                    if (i as usize) < SMALL_ACCESS_SIZE {
                        let node = small_access.snodes[i as usize];
                        println!("{}SmallAccess({})",
                            (0..depth).map(|_| ' ').collect::<String>(),
                            c as u8 as char);
                        Self::print_structure(node, depth + 1);
                    }
                }
            },
            BurstTrieNodeType::Empty => ()
        }
    }
}

fn opt_binary_search_by<K, F>(slice: &[K], mut f: F) -> Result<usize, usize>
    where F: FnMut(&K) -> Ordering
{
    let mut base : usize = 0;
    let mut lim : usize = slice.len();

    while lim != 0 {
        let ix = base + (lim >> 1);
        match f(unsafe { &slice.get_unchecked(ix) }) {
            Ordering::Equal => return Ok(ix),
            Ordering::Less => {
                base = ix + 1;
                lim -= 1;
            }
            Ordering::Greater => ()
        }
        lim >>= 1;
    }
    Err(base)
}

/// Bytewise slice comparison.
/// NOTE: This uses the system's memcmp, which is currently dramatically
/// faster than comparing each byte in a loop.
#[inline(always)]
fn cmp_slice_offset(a: &[u8], b: &[u8], offset: usize) -> Ordering {
    // NOTE: In theory n should be libc::size_t and not usize, but libc is not available here
    #[allow(improper_ctypes)]
    extern { fn memcmp(s1: *const u8, s2: *const u8, n: usize) -> i32; }
    let cmp = unsafe {
        memcmp(
            a.as_ptr().offset(offset as isize),
            b.as_ptr().offset(offset as isize),
            cmp::min(a.len(), b.len()) - offset
        )
    };

    if cmp == 0 {
        a.len().cmp(&b.len())
    } else if cmp < 0 {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

impl<K, V> ContainerNode<K, V> where K: AsRef<[u8]> {
    fn from_key_value(key: K, value: V) -> Box<Self> {
        Box::new(ContainerNode {
            _type: BurstTrieNodeType::Container,
            items: vec![(key, value)]
        })
    }

    fn burst(&mut self, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> *mut BurstTrieNode<K, V> {
        let container = unsafe { Box::from_raw(self as *mut Self) };
        let mut cardinality = 0;
        if CONTAINER_SIZE > SMALL_ACCESS_SIZE {
            // otherwise the code inside is useless
            let mut index = [false; ALPHABET_SIZE];
            for &(ref key, _) in &container.items {
                if depth < key.as_ref().len() {
                    let idx = key.as_ref()[depth] as usize;
                    if ! index[idx] {
                        index[idx] = true;
                        cardinality += 1;
                    }
                } else {
                    cardinality += 1;
                }
            }
        }
        unsafe {
            if cardinality > SMALL_ACCESS_SIZE {
                *node_ref = Box::into_raw(AccessNode::from_container(container, depth)) as *mut _;
            } else {
                *node_ref = Box::into_raw(SmallAccessNode::from_container(container, depth)) as *mut _;
            }
            *node_ref
        }
    }

    fn insert(&mut self, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> {
        // optimize insertions at the end
        // helps in seq insert and node bursting
        let seq_insert = match self.items.last_mut() {
            Some(&mut (ref last_key, ref mut last_value)) =>
                match cmp_slice_offset(last_key.as_ref(), key.as_ref(), depth) {
                    Ordering::Equal => {
                        return Some(mem::replace(last_value, value));
                    },
                    Ordering::Less => true,
                    Ordering::Greater => false
                },
            None => true
        };

        let insert_pos = if seq_insert {
            self.items.len()
        } else {
            // binary search doesn't have to check the last element due to the previous
            let res_bs = opt_binary_search_by(&self.items[..self.items.len() - 1], |other| {
                cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
            });
            match res_bs {
                Ok(pos) => {
                    let old_value = unsafe { self.items.get_unchecked_mut(pos) };
                    return Some(mem::replace(&mut old_value.1, value));
                },
                Err(pos) => pos
            }
        };

        if self.items.len() >= CONTAINER_SIZE {
            BurstTrieNode::insert(self.burst(depth, node_ref), key, value, depth, node_ref)
        } else {
            self.items.insert(insert_pos, (key, value));
            None
        }
    }

    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> where Q: AsRef<[u8]> {
        let res_bs = opt_binary_search_by(&self.items, |other| {
            cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
        });
        match res_bs {
            Ok(pos) => Some(self.items.remove(pos).1),
            Err(_) => None
        }
    }

    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: AsRef<[u8]> {
        let res_bs = opt_binary_search_by(&self.items, |other| {
            cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
        });
        if let Ok(pos) = res_bs {
            Some(unsafe { &self.items.get_unchecked(pos).1 })
        } else {
            None
        }
    }
}

impl<K, V> AccessNode<K, V> where K: AsRef<[u8]> {
    fn from_container(container: Box<ContainerNode<K, V>>, depth: usize) -> Box<Self> {
        let mut access_node = Box::new(AccessNode {
            _type: BurstTrieNodeType::Access,
            nodes: unsafe { mem::zeroed() },
            terminator: None
        });
        for (key, value) in container.items {
            access_node.insert(key, value, depth, ptr::null_mut());
        }
        access_node
    }

    fn from_small(mut small: Box<SmallAccessNode<K, V>>) -> Box<Self> {
        let mut access_node = Box::new(AccessNode {
            _type: BurstTrieNodeType::Access,
            nodes: unsafe { mem::zeroed() },
            terminator: small.terminator.take()
        });
        for idx in (0..ALPHABET_SIZE) {
            let small_idx = small.index[idx] as usize;
            if small_idx < SMALL_ACCESS_SIZE {
                access_node.nodes[idx] = mem::replace(&mut small.snodes[small_idx], ptr::null_mut());
            }
        }
        access_node
    }

    fn insert(&mut self, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> {
        // depth is always <= key.len
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::insert(self.nodes[idx], key, value, depth + 1, &mut self.nodes[idx])
        } else if let Some((_, ref mut old_value)) = self.terminator {
            Some(mem::replace(old_value, value))
        } else {
            self.terminator = Some((key, value));
            None
        }
    }

    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::remove(self.nodes[idx], key, depth + 1, &mut self.nodes[idx])
        } else if let Some((_, old_value)) = self.terminator.take() {
            Some(old_value)
        } else {
            None
        }
    }

    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::get(self.nodes[idx], key, depth + 1)
        } else if let Some((_, ref v)) = self.terminator {
            Some(v)
        } else {
            None
        }
    }
}

impl<K, V> Drop for AccessNode<K, V> where K: AsRef<[u8]> {
    fn drop(&mut self) {
        for &ptr in self.nodes.iter() {
            BurstTrieNode::drop(ptr);
        }
    }
}

impl<K, V> SmallAccessNode<K, V> where K: AsRef<[u8]> {
    fn from_container(container: Box<ContainerNode<K, V>>, depth: usize) -> Box<Self> {
        let mut access_node = Box::new(SmallAccessNode {
            _type: BurstTrieNodeType::SmallAccess,
            len: 0,
            index: [SMALL_ACCESS_SIZE as u8; ALPHABET_SIZE],
            snodes: unsafe { mem::zeroed() },
            terminator: None
        });
        for (key, value) in container.items {
            access_node.insert(key, value, depth, ptr::null_mut());
        }
        access_node
    }

    fn grow(&mut self, node_ref: BurstTrieNodeRef<K, V>) -> *mut BurstTrieNode<K, V> {
        unsafe {
            let small_access = Box::from_raw(self as *mut Self);
            *node_ref = Box::into_raw(AccessNode::from_small(small_access))  as *mut _;
            *node_ref
        }
    }

    fn insert(&mut self, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> {
        // depth is always <= key.len
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            
            let small_idx = if (self.index[idx] as usize) < SMALL_ACCESS_SIZE {
                self.index[idx] as usize
            } else if (self.len as usize) < SMALL_ACCESS_SIZE {
                self.index[idx] = self.len as u8;
                let prev_len = self.len;
                self.len += 1;
                prev_len as usize
            } else {
                return BurstTrieNode::insert(self.grow(node_ref), key, value, depth, node_ref);
            };
            BurstTrieNode::insert(self.snodes[small_idx], key, value, depth + 1, &mut self.snodes[small_idx])
        } else if let Some((_, ref mut old_value)) = self.terminator {
            Some(mem::replace(old_value, value))
        } else {
            self.terminator = Some((key, value));
            None
        }
    }

    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize, node_ref: BurstTrieNodeRef<K, V>) -> Option<V> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            let small_idx = self.index[idx] as usize;
            if small_idx < SMALL_ACCESS_SIZE {
                BurstTrieNode::remove(self.snodes[small_idx], key, depth + 1, &mut self.snodes[small_idx])
            } else {
                None
            }
        } else if let Some((_, old_value)) = self.terminator.take() {
            Some(old_value)
        } else {
            None
        }
    }

    fn get<Q: ?Sized>(&self, key: &Q, depth: usize) -> Option<&V> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            let small_idx = self.index[idx] as usize;
            if small_idx < SMALL_ACCESS_SIZE {
                BurstTrieNode::get(self.snodes[small_idx], key, depth + 1)
            } else {
                None
            }
        } else if let Some((_, ref v)) = self.terminator {
            Some(v)
        } else {
            None
        }
    }
}

impl<K, V> Drop for SmallAccessNode<K, V> where K: AsRef<[u8]> {
    fn drop(&mut self) {
        for &ptr in self.snodes.iter() {
            BurstTrieNode::drop(ptr);
        }
    }
}

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for BurstTrieMap<K, V> where K: AsRef<[u8]>, Q: AsRef<[u8]> {
    type Output = V;

    fn index(&self, index: &Q) -> &V {
        self.get(index).unwrap()
    }
}

impl<'a, K, V, Q: ?Sized> IndexMut<&'a Q> for BurstTrieMap<K, V> where K: AsRef<[u8]>, Q: AsRef<[u8]> {
    fn index_mut(&mut self, index: &Q) -> &mut V {
        self.get_mut(index).unwrap()
    }
}

impl<K, V> Default for BurstTrieMap<K, V> where K: AsRef<[u8]> {
    #[inline]
    fn default() -> BurstTrieMap<K, V> { BurstTrieMap::new() }
}

// pub struct Iter<'a, K: 'a, V: 'a> where K: AsRef<[u8]> {
//     stack: Vec<&'a BurstTrieNode<K, V>>,
//     container_iter: Option<slice::Iter<'a, (K, V)>>,
//     remaining_len: usize
// }

// impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> where K: AsRef<[u8]> {}

// impl<'a, K, V> Iterator for Iter<'a, K, V> where K: AsRef<[u8]> {
//     type Item = (&'a K, &'a V);

//     fn next(&mut self) -> Option<(&'a K, &'a V)> {
//         if let Some(ref mut iter) = self.container_iter {
//             let next = iter.next();
//             if let Some(&(ref key, ref value)) = next {
//                 self.remaining_len -= 1;
//                 return Some((key, value));
//             }
//         }

//         while let Some(node) = self.stack.pop() {
//             match *node {
//                 BurstTrieNode::Container(box ref container) => {
//                     let mut iter = container.items.iter();
//                     let next = iter.next();
//                     mem::replace(&mut self.container_iter, Some(iter)); 
//                     if let Some(&(ref key, ref value)) = next {
//                         self.remaining_len -= 1;
//                         return Some((key, value));
//                     }
//                 },
//                 BurstTrieNode::Access(box ref access) => {
//                     // add to stack in reverse order
//                     for i in (1..ALPHABET_SIZE + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         match access.nodes[idx] {
//                             ref node @ BurstTrieNode::Container(_) |
//                             ref node @ BurstTrieNode::SmallAccess(_) |
//                             ref node @ BurstTrieNode::Access(_) => {
//                                 self.stack.push(node);
//                             },
//                             BurstTrieNode::Empty => ()
//                         }
//                     }

//                     if let Some((ref key, ref value)) = access.terminator {
//                         self.remaining_len -= 1;
//                         return Some((key, value));
//                     }
//                 },
//                 BurstTrieNode::SmallAccess(box ref small) => {
//                     // add to stack in reverse order
//                     for i in (1..ALPHABET_SIZE + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         let small_idx = small.index[idx] as usize;
//                         if small_idx < SMALL_ACCESS_SIZE {
//                             match small.snodes[small_idx] {
//                                 ref node @ BurstTrieNode::Container(_) |
//                                 ref node @ BurstTrieNode::SmallAccess(_) |
//                                 ref node @ BurstTrieNode::Access(_) => {
//                                     self.stack.push(node);
//                                 },
//                                 BurstTrieNode::Empty => ()
//                             }
//                         }
//                     }

//                     if let Some((ref key, ref value)) = small.terminator {
//                         self.remaining_len -= 1;
//                         return Some((key, value));
//                     }
//                 },
//                 BurstTrieNode::Empty => ()
//             }
//         }
//         None
//     }

//     #[inline]
//     fn size_hint(&self) -> (usize, Option<usize>) {
//         (self.remaining_len, Some(self.remaining_len))
//     }
// }

// pub struct IntoIter<K, V> where K: AsRef<[u8]> {
//     stack: Vec<BurstTrieNode<K, V>>,
//     container_iter: Option<vec::IntoIter<(K, V)>>,
//     remaining_len: usize
// }

// impl<K, V> ExactSizeIterator for IntoIter<K, V> where K: AsRef<[u8]> {}

// impl<K, V> Iterator for IntoIter<K, V> where K: AsRef<[u8]> {
//     type Item = (K, V);

//     fn next(&mut self) -> Option<(K, V)> {
//         if let Some(ref mut iter) = self.container_iter {
//             let next = iter.next();
//             if next.is_some() {
//                 self.remaining_len -= 1;
//                 return next;
//             }
//         }

//         while let Some(node) = self.stack.pop() {
//             match node {
//                 BurstTrieNode::Container(container) => {
//                     let mut iter = container.items.into_iter();
//                     let next = iter.next();
//                     mem::replace(&mut self.container_iter, Some(iter));
//                     if next.is_some() {
//                         self.remaining_len -= 1;
//                         return next;
//                     }
//                 },
//                 BurstTrieNode::Access(box mut access) => {
//                     // add to stack in reverse order
//                     for i in (1..ALPHABET_SIZE + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         let node = mem::replace(&mut access.nodes[idx], BurstTrieNode::Empty);
//                         match node {
//                             BurstTrieNode::Container(_) |
//                             BurstTrieNode::SmallAccess(_) |
//                             BurstTrieNode::Access(_) => {
//                                 self.stack.push(node);
//                             },
//                             BurstTrieNode::Empty => ()
//                         }
//                     }


//                     if access.terminator.is_some() {
//                         self.remaining_len -= 1;
//                         return access.terminator;
//                     }
//                 },
//                 BurstTrieNode::SmallAccess(box mut small) => {
//                     // add to stack in reverse order
//                     for i in (1..ALPHABET_SIZE + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         let small_idx = small.index[idx] as usize;
//                         if small_idx < SMALL_ACCESS_SIZE {
//                             let node = mem::replace(&mut small.snodes[small_idx], BurstTrieNode::Empty);
//                             match node {
//                                 BurstTrieNode::Container(_) |
//                                 BurstTrieNode::SmallAccess(_) |
//                                 BurstTrieNode::Access(_) => {
//                                     self.stack.push(node);
//                                 },
//                                 BurstTrieNode::Empty => ()
//                             }
//                         }
//                     }

//                     if small.terminator.is_some() {
//                         self.remaining_len -= 1;
//                         return small.terminator;
//                     }
//                 },
//                 BurstTrieNode::Empty => ()
//             }
//         }
//         None
//     }

//     #[inline]
//     fn size_hint(&self) -> (usize, Option<usize>) {
//         (self.remaining_len, Some(self.remaining_len))
//     }
// }

// pub struct Range<'a, K: 'a, V: 'a, Q: 'a + ?Sized> where K: AsRef<[u8]>, Q: AsRef<[u8]> {
//     stack: VecDeque<(&'a BurstTrieNode<K, V>, u16, bool, u16, u16)>,
//     curr_item: Option<(&'a BurstTrieNode<K, V>, u16, bool, u16, u16)>,
//     min: Bound<&'a Q>,
//     max: Bound<&'a Q>
// }

// impl<'a, K, V, Q: ?Sized> Range<'a, K, V, Q> where K: AsRef<[u8]>, Q: AsRef<[u8]> {

//     fn new(root: &'a BurstTrieNode<K, V>, min: Bound<&'a Q>, max: Bound<&'a Q>) -> Range<'a, K, V, Q> {
//         let mut range = Range {
//             stack: VecDeque::new(),
//             curr_item: None,
//             min: min,
//             max: max
//         };

//         match *root {
//             BurstTrieNode::Container(box ref container) =>
//                 range.stack.push_back((root, 0, true, 0, container.items.len() as u16)),
//             BurstTrieNode::Access(_) |
//             BurstTrieNode::SmallAccess(_)  =>
//                 range.stack.push_back((root, 0, true, 0, ALPHABET_SIZE as u16)),
//             BurstTrieNode::Empty => return range
//         }

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
//                 BurstTrieNode::Container(box ref container) => {
//                     let res_bs = opt_binary_search_by(&container.items, |other| {
//                         other.0.as_ref()[depthsz..].cmp(&min_key.as_ref()[depthsz..])
//                     });
//                     let start_pos = match res_bs {
//                         Ok(pos) if ! min_included => pos + 1,
//                         Ok(pos) | Err(pos) => pos
//                     };
//                     self.stack.push_back((node, depth, false, start_pos as u16, container.items.len() as u16));
//                     // can only hit a container once
//                     return;
//                 },
//                 BurstTrieNode::Access(box ref access) => {
//                     if depthsz < min_key.as_ref().len() {
//                         let min_key_byte = min_key.as_ref()[depthsz] as usize;
//                         self.stack.push_back((node, depth, false, min_key_byte as u16 + 1, ALPHABET_SIZE as u16));
//                         match access.nodes[min_key_byte] {
//                             BurstTrieNode::Container(box ref container) =>
//                                 self.stack.push_back((&access.nodes[min_key_byte], depth + 1, false, 0, container.items.len() as u16)),
//                             BurstTrieNode::Access(_) |
//                             BurstTrieNode::SmallAccess(_) =>
//                                 self.stack.push_back((&access.nodes[min_key_byte], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                             BurstTrieNode::Empty => return // exit
//                         }
//                     } else {
//                         // re-add node to the stack with correct terminator and exit
//                         self.stack.push_back((node, depth, min_included, 0, ALPHABET_SIZE as u16));
//                         return;
//                     }
//                 },
//                 BurstTrieNode::SmallAccess(box ref small) => {
//                     if depthsz < min_key.as_ref().len() {
//                         let min_key_byte = min_key.as_ref()[depthsz] as usize;
//                         self.stack.push_back((node, depth, false, min_key_byte as u16 + 1, ALPHABET_SIZE as u16));
//                         let small_idx = small.index[min_key_byte] as usize;
//                         if small_idx < SMALL_ACCESS_SIZE {
//                             match small.snodes[small_idx] {
//                                 BurstTrieNode::Container(box ref container) =>
//                                     self.stack.push_back((&small.snodes[small_idx], depth + 1, false, 0, container.items.len() as u16)),
//                                 BurstTrieNode::Access(_) |
//                                 BurstTrieNode::SmallAccess(_) =>
//                                     self.stack.push_back((&small.snodes[small_idx], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                                 BurstTrieNode::Empty => return // exit
//                             }
//                         }
//                     } else {
//                         // re-add node to the stack with correct terminator and exit
//                         self.stack.push_back((node, depth, min_included, 0, ALPHABET_SIZE as u16));
//                         return;
//                     }
//                 },
//                 BurstTrieNode::Empty => ()
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
//                 BurstTrieNode::Container(box ref container) => {
//                     let res_bs = opt_binary_search_by(&container.items, |other| {
//                         other.0.as_ref()[depthsz..].cmp(&max_key.as_ref()[depthsz..])
//                     });
//                     let end_pos = match res_bs {
//                         Ok(pos) if max_included => pos + 1,
//                         Ok(pos) | Err(pos) => pos
//                     };
//                     self.stack.push_front((node, depth, false, start_pos, end_pos as u16));
//                     // can only hit a container once
//                     return;
//                 },
//                 BurstTrieNode::Access(box ref access) => {
//                     if depthsz < max_key.as_ref().len() {
//                         let max_key_byte = max_key.as_ref()[depthsz] as usize;
//                         self.stack.push_front((node, depth, terminator, start_pos, max_key_byte as u16));
//                         match access.nodes[max_key_byte] {
//                             BurstTrieNode::Container(box ref container) =>
//                                 self.stack.push_front((&access.nodes[max_key_byte], depth + 1, false, 0, container.items.len() as u16)),
//                             BurstTrieNode::Access(_) |
//                             BurstTrieNode::SmallAccess(_) =>
//                                 self.stack.push_front((&access.nodes[max_key_byte], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                             BurstTrieNode::Empty => return // exit
//                         }
//                     } else {
//                         // re-add node to the stack with correct terminator and exit
//                         self.stack.push_front((node, depth, max_included, 0, 0));
//                         return;
//                     }
//                 },
//                 BurstTrieNode::SmallAccess(box ref small) => {
//                     if depthsz < max_key.as_ref().len() {
//                         let max_key_byte = max_key.as_ref()[depthsz] as usize;
//                         self.stack.push_front((node, depth, terminator, start_pos, max_key_byte as u16));
//                         let small_idx = small.index[max_key_byte] as usize;
//                         if small_idx < SMALL_ACCESS_SIZE {
//                             match small.snodes[small_idx] {
//                                 BurstTrieNode::Container(box ref container) =>
//                                     self.stack.push_front((&small.snodes[small_idx], depth + 1, false, 0, container.items.len() as u16)),
//                                 BurstTrieNode::Access(_) |
//                                 BurstTrieNode::SmallAccess(_) =>
//                                     self.stack.push_front((&small.snodes[small_idx], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                                 BurstTrieNode::Empty => return // exit
//                             }
//                         }
//                     } else {
//                         // re-add node to the stack with correct terminator and exit
//                         self.stack.push_front((node, depth, max_included, 0, 0));
//                         return;
//                     }
//                 },
//                 BurstTrieNode::Empty => ()
//             }
//         }
//     }

//     fn find_next(&mut self) -> Option<(&'a K, &'a V)> {
//         if let Some((&BurstTrieNode::Container(box ref container), _, _, ref mut start_pos, end_pos)) = self.curr_item {
//             if *start_pos < end_pos {
//                 let (ref key, ref value) = container.items[*start_pos as usize];
//                 *start_pos += 1; // advance iterator
//                 return Some((key, value));
//             }
//         }

//         while let Some((node, depth, terminator, start_pos, end_pos)) = self.stack.pop_back() {
//             match *node {
//                 BurstTrieNode::Container(box ref container) => {
//                     if start_pos < end_pos {
//                         self.curr_item = Some((node, depth, terminator, start_pos + 1, end_pos));
//                         let (ref key, ref value) = container.items[start_pos as usize];
//                         return Some((key, value));
//                     }
//                 },
//                 BurstTrieNode::Access(box ref access) => {
//                     // add to stack in reverse order
//                     for i in ((ALPHABET_SIZE - end_pos as usize) + 1 .. (ALPHABET_SIZE - start_pos as usize) + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         match access.nodes[idx] {
//                             BurstTrieNode::Container(box ref container) =>
//                                 self.stack.push_back((&access.nodes[idx], depth + 1, false, 0, container.items.len() as u16)),
//                             BurstTrieNode::Access(_) |
//                             BurstTrieNode::SmallAccess(_) =>
//                                 self.stack.push_back((&access.nodes[idx], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                             BurstTrieNode::Empty => ()
//                         }
//                     }

//                     if terminator {
//                         if let Some((ref key, ref value)) = access.terminator {
//                             return Some((key, value));
//                         }
//                     }
//                 },
//                 BurstTrieNode::SmallAccess(box ref small) => {
//                     // add to stack in reverse order
//                     for i in ((ALPHABET_SIZE - end_pos as usize) + 1 .. (ALPHABET_SIZE - start_pos as usize) + 1) {
//                         let idx = ALPHABET_SIZE - i;
//                         let small_idx = small.index[idx] as usize;
//                         if small_idx < SMALL_ACCESS_SIZE {
//                             match small.snodes[small_idx] {
//                                 BurstTrieNode::Container(box ref container) =>
//                                     self.stack.push_back((&small.snodes[small_idx], depth + 1, false, 0, container.items.len() as u16)),
//                                 BurstTrieNode::Access(_) |
//                                 BurstTrieNode::SmallAccess(_) =>
//                                     self.stack.push_back((&small.snodes[small_idx], depth + 1, true, 0, ALPHABET_SIZE as u16)),
//                                 BurstTrieNode::Empty => ()
//                             }
//                         }
//                     }

//                     if terminator {
//                         if let Some((ref key, ref value)) = small.terminator {
//                             return Some((key, value));
//                         }
//                     }
//                 },
//                 BurstTrieNode::Empty => ()
//             }
//         }

//         None
//     }
// }

// impl<'a, K, V, Q: ?Sized> Iterator for Range<'a, K, V, Q> where K: AsRef<[u8]>, Q: AsRef<[u8]> {
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
    use super::{BurstTrieMap, BurstTrieNode};
    use std::collections::Bound;
    use rand::*;

    // #[test]
    // fn test_iter() {
    //     let mut map = BurstTrieMap::new();

    //     for i in (100000..999999) {
    //         map.insert(i.to_string(), i);
    //     }

    //     let mut i = 100000usize;
    //     for (key, value) in map.iter() {
    //         assert_eq!(key.parse::<usize>().unwrap(), i);
    //         assert_eq!(*value, i);
    //         i += 1;
    //     }
    //     assert_eq!(i, 999999);
    // }

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

    //     for _ in (0..1000) {
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

    // #[test]
    // fn test_into_iter() {
    //     let mut map = BurstTrieMap::new();

    //     // use a dropable value so it crashes if double drop
    //     for i in (100000..999999) {
    //         map.insert(i.to_string(), i.to_string());
    //     }

    //     let mut i = 100000usize;
    //     for (key, value) in map.into_iter() {
    //         assert_eq!(key.parse::<usize>().unwrap(), i);
    //         assert_eq!(value.parse::<usize>().unwrap(), i);
    //         i += 1;
    //     }
    //     assert_eq!(i, 999999);
    // }

    // #[test]
    // fn test_keys() {
    //     let mut map = BurstTrieMap::new();

    //     for i in (100000..999999) {
    //         map.insert(i.to_string(), i);
    //     }

    //     let mut i = 100000usize;
    //     for key in map.keys() {
    //         assert_eq!(key.parse::<usize>().unwrap(), i);
    //         i += 1;
    //     }
    //     assert_eq!(i, 999999);
    // }

    // #[test]
    // fn test_values() {
    //     let mut map = BurstTrieMap::new();

    //     for i in (100000..999999) {
    //         map.insert(i.to_string(), i);
    //     }

    //     let mut i = 100000usize;
    //     for value in map.values() {
    //         assert_eq!(*value, i);
    //         i += 1;
    //     }
    //     assert_eq!(i, 999999);
    // }

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

    // map_iter_bench!(burst_iter_10000, 20, 100, 10000, BurstTrieMap);
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

    use std::collections::HashMap;
    map_get_rnd_bench!(hash_get_short_1000, 5, 15, 1000, HashMap);
    map_get_rnd_bench!(hash_get_short_10000, 5, 15, 10000, HashMap);
    map_get_rnd_bench!(hash_get_short_100000, 5, 15, 100000, HashMap);
    map_get_rnd_bench!(hash_get_medium_1000, 20, 100, 1000, HashMap);
    map_get_rnd_bench!(hash_get_medium_10000, 20, 100, 10000, HashMap);
    map_get_rnd_bench!(hash_get_medium_100000, 20, 100, 100000, HashMap);
    map_insert_rnd_bench!(hash_insert_short_1000, 5, 15, 1000, HashMap);
    map_insert_rnd_bench!(hash_insert_short_10000, 5, 15, 10000, HashMap);
    map_insert_rnd_bench!(hash_insert_short_100000, 5, 15, 100000, HashMap);
    map_insert_rnd_bench!(hash_insert_medium_1000, 20, 100, 1000, HashMap);
    map_insert_rnd_bench!(hash_insert_medium_10000, 20, 100, 10000, HashMap);
    map_insert_rnd_bench!(hash_insert_medium_100000, 20, 100, 100000, HashMap);

    map_get_rnd_bench!(hash_get_prefix_medium_10000, 20, 100, 10000, HashMap, "https://www.");
    map_get_rnd_bench!(hash_get_prefix_medium_100000, 20, 100, 100000, HashMap, "https://www.");
    map_insert_rnd_bench!(hash_insert_prefix_medium_10000, 20, 100, 10000, HashMap, "https://www.");
    map_insert_rnd_bench!(hash_insert_prefix_medium_100000, 20, 100, 100000, HashMap, "https://www.");



    // map_iter_bench!(btree_iter_10000, 20, 100, 10000, BTreeMap);
    // map_range_bench!(btree_range_10000, 20, 100, 10000, BTreeMap);
}
