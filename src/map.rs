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
use std::sync::Arc;
use std::sync::atomic::{self, AtomicUsize};
use std::cmp::{self, Ordering};
use std::default::Default;
use std::ops::{Index, IndexMut};
use std::marker;

use crossbeam::mem::epoch::{self, Atomic, Owned, Shared};
use spin;
use arrayvec::ArrayVec;
// use permutation;

const ALPHABET_SIZE: usize = 256;
const CONTAINER_SIZE: usize = 32;

/// An BurstTrie implementation of an ordered map. Specialized for byte ordered types.
///
/// See module level docs for details.
pub struct BurstTrieMap<K, V> where K: AsRef<[u8]> {
    root: Atomic<BurstTrieNode<K, V>>,
    len: AtomicUsize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum BurstTrieNodeType {
    Empty = 0,
    Container,
    Access,
}

struct BurstTrieNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    marker: marker::PhantomData<(K, V)>,
}

struct ContainerNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    rw_lock: spin::RwLock<()>,
    items: ArrayVec<[Arc<(K, V)>; CONTAINER_SIZE]>,
}

struct AccessNode<K, V> where K: AsRef<[u8]> {
    _type: BurstTrieNodeType,
    lock: spin::Mutex<()>,
    nodes: [Atomic<BurstTrieNode<K, V>>; ALPHABET_SIZE],
    terminator: Option<Arc<(K, V)>>,
}


impl<K, V> BurstTrieMap<K, V> where K: AsRef<[u8]> {
    
    /// Returns a new empty BurstTrieMap
    pub fn new() -> BurstTrieMap<K, V> {
        BurstTrieMap {
            root: Atomic::null(),
            len: AtomicUsize::new(0),
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
    pub fn insert(&mut self, key: K, value: V) -> Option<Arc<(K, V)>> {
        let guard = epoch::pin();
        let opt_old_value = BurstTrieNode::insert(
            self.root.load(atomic::Ordering::Acquire, &guard),
            key, value, 0, &self.root, &guard);
        if opt_old_value.is_none() {
            self.len.fetch_add(1, atomic::Ordering::Relaxed);
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
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        let guard = epoch::pin();
        BurstTrieNode::get(
            self.root.load(atomic::Ordering::Acquire, &guard),
            key, 0, &guard)
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
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        let guard = epoch::pin();
        let opt_old_value = BurstTrieNode::remove(
            self.root.load(atomic::Ordering::Acquire, &guard),
            key, 0, &mut self.root, &guard);
        if opt_old_value.is_some() {
            self.len.fetch_sub(1, atomic::Ordering::Relaxed);
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
        self.len.load(atomic::Ordering::Relaxed)
    }

    /// Returns *true* if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
        let guard = epoch::pin();
        BurstTrieNode::drop(self.root.swap(None, atomic::Ordering::Acquire, &guard), &guard);
        // BROKEN
        self.len.store(0, atomic::Ordering::Relaxed)
    }

    pub fn print_structure(&self) {
        let guard = epoch::pin();
        BurstTrieNode::print_structure(
            self.root.load(atomic::Ordering::Acquire, &guard), 0, &guard);
    }

}

impl<K, V> Drop for BurstTrieMap<K, V> where K: AsRef<[u8]> {
    fn drop(&mut self) {
        self.clear()
    }
}

type BurstTrieNodeRef<'a, K, V> = &'a Atomic<BurstTrieNode<K, V>>;

impl<K, V> BurstTrieNode<K, V> where K: AsRef<[u8]>  {
    #[inline]
    fn _type(n: Option<Shared<Self>>) -> BurstTrieNodeType {
        if n.is_none() || n.unwrap().as_raw().is_null() {
            BurstTrieNodeType::Empty
        } else {
            debug_assert!(n.unwrap()._type != BurstTrieNodeType::Empty);
            n.unwrap()._type
        }
    }

    #[inline]
    fn as_container(n: Shared<Self>) -> &mut ContainerNode<K, V> {
        debug_assert!(n._type == BurstTrieNodeType::Container);
        unsafe { mem::transmute(n) }
    }

    #[inline]
    fn as_access(n: Shared<Self>) -> &mut AccessNode<K, V> {
        debug_assert!(n._type == BurstTrieNodeType::Access);
        unsafe { mem::transmute(n) }
    }

    #[inline]
    fn get<Q: ?Sized>(n: Option<Shared<Self>>, key: &Q, depth: usize, guard: &epoch::Guard) -> Option<Arc<(K, V)>>
    where Q: AsRef<[u8]> {
        match Self::_type(n) {
            BurstTrieNodeType::Container => {
                Self::as_container(n.unwrap()).get(key, depth, guard)
            },
            BurstTrieNodeType::Access => {
                Self::as_access(n.unwrap()).get(key, depth, guard)
            },
            BurstTrieNodeType::Empty => None,
        }
    }

    #[inline]
    fn insert_pair(n: Option<Shared<Self>>, pair: Arc<(K, V)>, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &epoch::Guard) {
        match Self::_type(n) {
            BurstTrieNodeType::Empty => {
                let mut container = ContainerNode::new();
                container.insert_pair(pair, depth, node_ref, guard);
                unsafe {
                    register_allocation(mem::transmute_copy(&container));
                    node_ref.store(mem::transmute(container), atomic::Ordering::Release);
                }
            },
            BurstTrieNodeType::Container => {
                Self::as_container(n.unwrap()).insert_pair(pair, depth, node_ref, guard)
            },
            BurstTrieNodeType::Access => {
                Self::as_access(n.unwrap()).insert_pair(pair, depth, guard)
            },
        }
    }

    #[inline]
    fn insert(n: Option<Shared<Self>>, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &epoch::Guard) -> Option<Arc<(K, V)>> {
        match Self::_type(n) {
            BurstTrieNodeType::Empty => {
                let mut container = ContainerNode::new();
                container.insert(key, value, depth, node_ref, guard);
                unsafe {
                    register_allocation(mem::transmute_copy(&container));
                    node_ref.store(mem::transmute(container), atomic::Ordering::Release);
                }
                None
            },
            BurstTrieNodeType::Container => {
                Self::as_container(n.unwrap()).insert(key, value, depth, node_ref, guard)
            },
            BurstTrieNodeType::Access => {
                Self::as_access(n.unwrap()).insert(key, value, depth, guard)
            },
        }
    }

    #[inline]
    fn remove<Q: ?Sized>(n: Option<Shared<Self>>, key: &Q, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &epoch::Guard) -> Option<Arc<(K, V)>>
    where Q: AsRef<[u8]> {
        match Self::_type(n) {
            BurstTrieNodeType::Container => {
                Self::as_container(n.unwrap()).remove(key, depth, node_ref, guard)
            },
            BurstTrieNodeType::Access => {
                Self::as_access(n.unwrap()).remove(key, depth, guard)
            },
            BurstTrieNodeType::Empty => None,
        }
    }

    #[inline(never)]
    fn drop(n: Option<Shared<Self>>, guard: &epoch::Guard) {
        if let Some(n) = n {
            register_free(n.as_raw() as usize);
        }
        unsafe {
            match BurstTrieNode::_type(n) {
                BurstTrieNodeType::Container => {
                    println!("dropping {:?}", BurstTrieNode::_type(n));
                    drop(ptr::read(Self::as_container(n.unwrap())));
                    guard.unlinked::<Shared<ContainerNode<K, V>>>(mem::transmute(n.unwrap()));
                },
                BurstTrieNodeType::Access => {
                    println!("dropping {:?}", BurstTrieNode::_type(n));
                    for child in Self::as_access(n.unwrap()).nodes.iter() {
                        BurstTrieNode::drop(child.load(atomic::Ordering::Acquire, &guard), &guard);
                    }
                    drop(ptr::read(Self::as_access(n.unwrap())));
                    guard.unlinked::<Shared<AccessNode<K, V>>>(mem::transmute(n.unwrap()));
                },
                BurstTrieNodeType::Empty => ()
            }
        }
    }

    #[inline]
    fn print_structure(n: Option<Shared<Self>>, depth: usize, guard: &epoch::Guard) {
        match BurstTrieNode::_type(n) {
            BurstTrieNodeType::Container => {
                println!("{}Container(LEN {})",
                    (0..depth).map(|_| ' ').collect::<String>(),
                    Self::as_container(n.unwrap()).items.len());
            },
            BurstTrieNodeType::Access => {
                let access = Self::as_access(n.unwrap());
                for (c, node) in access.nodes.iter().enumerate() {
                    println!("{}Access({})",
                        (0..depth).map(|_| ' ').collect::<String>(),
                        c as u8 as char);
                    Self::print_structure(node.load(atomic::Ordering::Acquire, guard), depth + 1, guard);
                }
            },
            BurstTrieNodeType::Empty => ()
        }
    }
}

fn opt_binary_search_by<K, F>(slice: &[Arc<K>], mut f: F) -> Result<usize, usize>
    where F: FnMut(&K) -> Ordering
{
    let mut base: usize = 0;
    let mut lim: usize = slice.len();

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
    fn new() -> Owned<Self> {
        Owned::new(ContainerNode {
            _type: BurstTrieNodeType::Container,
            rw_lock: spin::RwLock::new(()),
            items: ArrayVec::new(),
        })
    }

    #[inline(never)]
    fn burst<'a>(&mut self, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &'a epoch::Guard) -> Option<Shared<'a, BurstTrieNode<K, V>>> {
        let mut access = AccessNode::new();
        for pair in self.items.drain(..) {
            access.insert_pair(pair, depth, guard);
        } 
        unsafe {
            register_allocation(mem::transmute_copy(&access));
            let result = node_ref.store_and_ref(
                mem::transmute(access), atomic::Ordering::Release, guard);
            BurstTrieNode::drop(
                mem::transmute::<&mut Self, Option<Shared<BurstTrieNode<K, V>>>>(self), guard);
            Some(result)
        }
    }

    fn insert_pair(&mut self, pair: Arc<(K, V)>, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &epoch::Guard) {
        if self.items.len() >= CONTAINER_SIZE {
            BurstTrieNode::insert_pair(
                self.burst(depth, node_ref, guard),
                pair, depth, node_ref, guard);
        } else {
            self.items.push(pair);
        }
    }

    fn insert(&mut self, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &epoch::Guard) -> Option<Arc<(K, V)>> {
        let insert_pos = {
            let res_bs = opt_binary_search_by(&self.items, |other| {
                cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
            });
            match res_bs {
                Ok(pos) => {
                    let old_value = unsafe { self.items.get_unchecked_mut(pos) };
                    return Some(mem::replace(old_value, Arc::new((key, value))));
                },
                Err(pos) => pos
            }
        };

        if self.items.len() >= CONTAINER_SIZE {
            BurstTrieNode::insert(
                self.burst(depth, node_ref, guard),
                key, value, depth, node_ref, guard)
        } else {
            self.items.insert(insert_pos, Arc::new((key, value)));
            None
        }
    }

    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize, _: BurstTrieNodeRef<K, V>, _: &epoch::Guard) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        let res_bs = opt_binary_search_by(&self.items, |other| {
            cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
        });
        match res_bs {
            Ok(pos) => self.items.remove(pos),
            Err(_) => None
        }
    }

    fn get<Q: ?Sized>(&self, key: &Q, depth: usize, _: &epoch::Guard) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        let res_bs = opt_binary_search_by(&self.items, |other| {
            cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
        });
        if let Ok(pos) = res_bs {
            Some(unsafe { self.items.get_unchecked(pos).clone() })
        } else {
            None
        }
    }
}

impl<K, V> AccessNode<K, V> where K: AsRef<[u8]> {
    fn new() -> Owned<Self> {
        Owned::new(AccessNode {
            _type: BurstTrieNodeType::Access,
            lock: spin::Mutex::new(()),
            nodes: unsafe { mem::zeroed() },
            terminator: None
        })
    }

    fn insert_pair(&mut self, pair: Arc<(K, V)>, depth: usize, guard: &epoch::Guard) {
        // depth is always <= key.len
        if depth < pair.0.as_ref().len() {
            let idx = pair.0.as_ref()[depth] as usize;
            BurstTrieNode::insert_pair(
                self.nodes[idx].load(atomic::Ordering::Acquire, guard),
                pair, depth + 1, &self.nodes[idx], guard);
        } else {
            self.terminator = Some(pair);
        }
    }

    fn insert(&mut self, key: K, value: V, depth: usize, guard: &epoch::Guard) -> Option<Arc<(K, V)>> {
        // depth is always <= key.len
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::insert(
                self.nodes[idx].load(atomic::Ordering::Acquire, guard),
                key, value, depth + 1, &self.nodes[idx], guard)
        } else {
            let _lock = self.lock.lock();
            mem::replace(&mut self.terminator, Some(Arc::new((key, value))))
        }
    }

    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize, guard: &epoch::Guard) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::remove(
                self.nodes[idx].load(atomic::Ordering::Acquire, guard),
                key, depth + 1, &self.nodes[idx], guard)
        } else {
            let _lock = self.lock.lock();
            self.terminator.take()
        }
    }

    fn get<Q: ?Sized>(&self, key: &Q, depth: usize, guard: &epoch::Guard) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::get(
                self.nodes[idx].load(atomic::Ordering::Acquire, guard),
                key, depth + 1, guard)
        } else {
            let _lock = self.lock.lock();
            self.terminator.clone()
        }
    }
}

impl<K, V> Default for BurstTrieMap<K, V> where K: AsRef<[u8]> {
    fn default() -> BurstTrieMap<K, V> { BurstTrieMap::new() }
}

use std::sync::Mutex;
use std::collections::HashSet;

lazy_static! {
    static ref CREATED: Mutex<HashSet<usize>> = Mutex::new(Default::default());
    static ref CLEANED: Mutex<HashSet<usize>> = Mutex::new(Default::default());
}

fn register_allocation(addr: usize) {
    assert!(CREATED.lock().unwrap().insert(addr));
}

fn register_free(addr: usize) {
    let t = CREATED.lock().unwrap().remove(&addr);
    match t {
        true => {
            println!("{:?} deallocated, ok: {}, left: {}",
                addr,
                CLEANED.lock().unwrap().insert(addr),
                CREATED.lock().unwrap().len());
        },
        false => {
            println!("{:?} not CREATED, in CLEANED {}", addr,
                CLEANED.lock().unwrap().contains(&addr));
            assert!(false);
        },
    } 
}

#[cfg(test)]
mod tests {
    use super::{BurstTrieMap, BurstTrieNode};
    // use std::collections::Bound;
    use rand::*;
    #[test]
    fn test_correctness() {
        let mut rng = weak_rng();
        for round in 0..3 {
            println!("round {} start", round);
            let mut trie = BurstTrieMap::new();
            for _ in 0..10000 {
                let key_len = rng.gen_range(1usize, 1000);
                let key = rng.gen_ascii_chars().take(key_len).collect::<String>();
                let value = rng.gen::<usize>();
                trie.insert(key.clone(), value);
                if let Some(r_value) = trie.get(&key) {
                    assert_eq!(value, r_value.1);
                } else {
                    panic!("key: {} not found", key);
                }
            }
            println!("round {} done", round);
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
        assert_eq!(m.get("2").unwrap().1, 11);
    }

    #[test]
    fn test_swap() {
        let mut m = BurstTrieMap::new();
        assert_eq!(m.insert("1", 2), None);
        assert_eq!(m.insert("1", 3).unwrap().1, 2);
        assert_eq!(m.insert("1", 4).unwrap().1, 3);
    }

    #[test]
    fn test_pop() {
        let mut m = BurstTrieMap::new();
        m.insert("1", 2);
        assert_eq!(m.remove("1").unwrap().1, 2);
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
