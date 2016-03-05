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
use std::marker::PhantomData;
use std::sync::Arc;
use std::sync::atomic::{self, AtomicUsize};
use std::cmp::{self, Ordering};
use std::default::Default;
// use std::ops::{Index, IndexMut};
use std::marker;

use crossbeam::mem::epoch::{self, Atomic, Owned, Shared};
use spin;
use arrayvec::ArrayVec;
// use permutation;

const ALPHABET_SIZE: usize = 256;
const CONTAINER_SIZE: usize = 16;

/// An BurstTrie implementation of an ordered map. Specialized for byte ordered types.
///
/// See module level docs for details.
pub struct BurstTrieMap<K, V> where K: AsRef<[u8]> {
    root: Atomic<BurstTrieNode<K, V>>,
    len: AtomicUsize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum BurstTrieNodeType {
    Empty = 0,
    Container,
    Access,
}

pub struct Wrapper<'a, K: 'a, V: 'a> {
    key: *const K,
    value: *const V,
    _guard: epoch::Guard,
    _phantom: PhantomData<&'a (K, V)>,
}

impl<'a, K, V> Wrapper<'a, K, V> {
    pub fn key(&self) -> &K {
        unsafe { mem::transmute(self.key) }
    }

    pub fn value(&self) -> &V {
        unsafe { mem::transmute(self.value) }
    }
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
    pub fn insert(&self, key: K, value: V) -> Option<Arc<(K, V)>> {
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
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<Wrapper<K, V>> where Q: AsRef<[u8]> {
        let guard = epoch::pin();
        let result = BurstTrieNode::get(
            self.root.load(atomic::Ordering::Acquire, &guard),
            key, 0, &guard);
        result.map(|r| Wrapper {
            key: r.0,
            value: r.1,
            _guard: guard,
            _phantom: PhantomData,
        })
    }

    pub fn find<Q: ?Sized>(&self, key: &Q) -> Option<Wrapper<K, V>> where Q: AsRef<[u8]> {
        self.get(key)
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
    pub fn remove<Q: ?Sized>(&self, key: &Q) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        let guard = epoch::pin();
        let opt_old_value = BurstTrieNode::remove(
            self.root.load(atomic::Ordering::Acquire, &guard),
            key, 0, &self.root, &guard);
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
    pub fn clear(&self) {
        let guard = epoch::pin();
        let drop_count = BurstTrieNode::drop(
            self.root.swap(None, atomic::Ordering::Acquire, &guard), &guard);
        self.len.fetch_sub(drop_count, atomic::Ordering::Relaxed);
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
        if n.is_none() {
            BurstTrieNodeType::Empty
        } else {
            debug_assert!(n.unwrap()._type != BurstTrieNodeType::Empty);
            n.unwrap()._type
        }
    }

    #[inline]
    #[allow(mutable_transmutes)]
    fn as_container(&self) -> &mut ContainerNode<K, V> {
        debug_assert!(self._type == BurstTrieNodeType::Container,
            "expected Container, got {:?}", self._type);
        unsafe { mem::transmute(self) }
    }

    #[inline]
    #[allow(mutable_transmutes)]
    fn as_access(&self) -> &mut AccessNode<K, V> {
        debug_assert!(self._type == BurstTrieNodeType::Access,
            "expected Access, got {:?}", self._type);
        unsafe { mem::transmute(self) }
    }

    #[inline]
    fn get<Q: ?Sized>(n: Option<Shared<Self>>, key: &Q, depth: usize, guard: &epoch::Guard) -> Option<(*const K, *const V)>
    where Q: AsRef<[u8]> {
        match Self::_type(n) {
            BurstTrieNodeType::Access => {
                n.unwrap().as_access().get(key, depth, guard)
            },
            BurstTrieNodeType::Container => {
                n.unwrap().as_container().get(key, depth, guard)
            },
            BurstTrieNodeType::Empty => None,
        }
    }

    /// Insert function guaranteed to be sequential insert and single threaded
    #[inline]
    fn insert_pair(n: Option<Shared<Self>>, pair: Arc<(K, V)>, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &epoch::Guard) {
        match Self::_type(n) {
            BurstTrieNodeType::Access => {
                n.unwrap().as_access().insert_pair(pair, depth, guard)
            },
            BurstTrieNodeType::Container => {
                n.unwrap().as_container().insert_pair(pair, depth, node_ref, guard)
            },
            BurstTrieNodeType::Empty => unsafe {
                let mut container = ContainerNode::new();
                container.insert_pair(pair, depth, node_ref, guard);
                register_allocation(mem::transmute_copy(&container));
                node_ref.store(mem::transmute(container), atomic::Ordering::Release);
            },
        }
    }

    // Good old insertion function
    #[inline]
    fn insert<'a>(mut n: Option<Shared<'a, Self>>, key: K, value: V, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &'a epoch::Guard) -> Option<Arc<(K, V)>> {
        loop {
            match Self::_type(n) {
                BurstTrieNodeType::Access => {
                    return n.unwrap().as_access().insert(key, value, depth, guard)
                },
                BurstTrieNodeType::Container => {
                    if let Some(_w_lock) = n.unwrap().as_container().rw_lock.try_write() {
                        return n.unwrap().as_container().insert(key, value, depth, node_ref, guard)
                    }
                },
                BurstTrieNodeType::Empty => unsafe {
                    let container: Owned<ContainerNode<K, V>> = ContainerNode::new();
                    register_allocation(mem::transmute_copy(&container));
                    if let Err(c) = node_ref.cas(n, mem::transmute(container), atomic::Ordering::AcqRel) {
                        register_free(mem::transmute(c));
                    }
                },
            }
            n = node_ref.load(atomic::Ordering::Acquire, guard);
        }
    }

    #[inline]
    fn remove<'a, Q: ?Sized>(mut n: Option<Shared<'a, Self>>, key: &Q, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &'a epoch::Guard) -> Option<Arc<(K, V)>>
    where Q: AsRef<[u8]> {
        loop {
            match Self::_type(n) {
                BurstTrieNodeType::Access => {
                    return n.unwrap().as_access().remove(key, depth, guard)
                },
                BurstTrieNodeType::Container => {
                    if let Some(_w_lock) = n.unwrap().as_container().rw_lock.try_write() {
                        return n.unwrap().as_container().remove(key, depth, guard)
                    }
                },
                BurstTrieNodeType::Empty => return None,
            }
            n = node_ref.load(atomic::Ordering::Acquire, guard);
        }
    }

    #[inline(never)]
    fn drop(n: Option<Shared<Self>>, guard: &epoch::Guard) -> usize {
        if let Some(n) = n {
            register_free(n.as_raw() as usize);
        }
        unsafe {
            match BurstTrieNode::_type(n) {
                BurstTrieNodeType::Access => {
                    let mut drop_count = n.unwrap().as_access().terminator.iter().count();
                    for child in n.unwrap().as_access().nodes.iter() {
                        drop_count += BurstTrieNode::drop(child.load(atomic::Ordering::Acquire, &guard), &guard);
                    }
                    // drop(ptr::read(n.unwrap().as_access()));
                    // guard.unlinked::<Shared<AccessNode<K, V>>>(mem::transmute(n.unwrap()));
                    drop_count
                },
                BurstTrieNodeType::Container => {
                    let drop_count = n.unwrap().as_container().items.len();
                    // drop(ptr::read(n.unwrap().as_container()));
                    // guard.unlinked::<Shared<ContainerNode<K, V>>>(mem::transmute(n.unwrap()));
                    drop_count
                },
                BurstTrieNodeType::Empty => 0
            }
        }
    }

    #[inline(never)]
    fn print_structure(n: Option<Shared<Self>>, depth: usize, guard: &epoch::Guard) {
        match BurstTrieNode::_type(n) {
            BurstTrieNodeType::Access => {
                for (c, node) in n.unwrap().as_access().nodes.iter().enumerate() {
                    println!("{}Access({:?})({})",
                        (0..depth).map(|_| ' ').collect::<String>(),
                        n.unwrap().as_raw(),
                        c as u8 as char);
                    Self::print_structure(node.load(atomic::Ordering::Acquire, guard), depth + 1, guard);
                }
            },
            BurstTrieNodeType::Container => {
                println!("{}Container({:?})(LEN {})",
                    (0..depth).map(|_| ' ').collect::<String>(),
                    n.unwrap().as_raw(),
                    n.unwrap().as_container().items.len());
            },
            BurstTrieNodeType::Empty => ()
        }
    }
}

// The expansion of this is quite a bit of code, so mark callers as non inlineable
#[inline]
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
#[inline]
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
    fn burst<'a>(&self, depth: usize, node_ref: BurstTrieNodeRef<K, V>, guard: &'a epoch::Guard) -> Option<Shared<'a, BurstTrieNode<K, V>>> {
        let mut access: Owned<AccessNode<K, V>> = AccessNode::new();
        for pair in self.items.iter() {
            access.insert_pair(unsafe { mem::transmute_copy(pair) }, depth, guard);
        }
        unsafe {
            register_allocation(mem::transmute_copy(&access));
            // guard.unlinked::<Shared<Self>>(mem::transmute(self));
            Some(node_ref.store_and_ref(
                mem::transmute(access), atomic::Ordering::Release, guard))
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

    #[inline(never)]
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

    #[inline(never)]
    fn remove<Q: ?Sized>(&mut self, key: &Q, depth: usize, _: &epoch::Guard) -> Option<Arc<(K, V)>> where Q: AsRef<[u8]> {
        let res_bs = opt_binary_search_by(&self.items, |other| {
            cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
        });
        match res_bs {
            Ok(pos) => self.items.remove(pos),
            Err(_) => None
        }
    }

    #[inline(never)]
    fn get<Q: ?Sized>(&self, key: &Q, depth: usize, _: &epoch::Guard) -> Option<(*const K, *const V)> where Q: AsRef<[u8]> {
        let _r_lock = self.rw_lock.read();
        let res_bs = opt_binary_search_by(&self.items, |other| {
            cmp_slice_offset(other.0.as_ref(), key.as_ref(), depth)
        });
        if let Ok(pos) = res_bs {
            Some(unsafe {
                let r = self.items.get_unchecked(pos);
                (&r.0 as *const _, &r.1 as *const _)
            })
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

    fn get<Q: ?Sized>(&self, key: &Q, depth: usize, guard: &epoch::Guard) -> Option<(*const K, *const V)> where Q: AsRef<[u8]> {
        if depth < key.as_ref().len() {
            let idx = key.as_ref()[depth] as usize;
            BurstTrieNode::get(
                self.nodes[idx].load(atomic::Ordering::Acquire, guard),
                key, depth + 1, guard)
        } else {
            let _lock = self.lock.lock();
            self.terminator.as_ref().map(|r| (&r.0 as *const _, &r.1 as *const _))
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
    // assert!(CREATED.lock().unwrap().insert(addr));
}

fn register_free(addr: usize) {
    // let t = CREATED.lock().unwrap().remove(&addr);
    // match t {
    //     true => {
    //         println!("{:?} deallocated, ok: {}, left: {}",
    //             addr,
    //             CLEANED.lock().unwrap().insert(addr),
    //             CREATED.lock().unwrap().len());
    //     },
    //     false => {
    //         println!("{:?} not CREATED, in CLEANED {}", addr,
    //             CLEANED.lock().unwrap().contains(&addr));
    //         assert!(false);
    //     },
    // }
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
            let trie = BurstTrieMap::new();
            for _ in 0..10000 {
                let key_len = rng.gen_range(1usize, 1000);
                let key = rng.gen_ascii_chars().take(key_len).collect::<String>();
                let value = rng.gen::<usize>();
                trie.insert(key.clone(), value);
                if let Some(r_value) = trie.get(&key) {
                    assert_eq!(&value, r_value.value());
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
        assert!(m.get("5").is_none());
    }

    #[test]
    fn find_not_found() {
        let m = BurstTrieMap::new();
        assert!(m.insert("1", 2).is_none());
        assert!(m.insert("5", 3).is_none());
        assert!(m.insert("9", 3).is_none());
        assert!(m.get("2").is_none());
    }

    #[test]
    fn test_len() {
        let m = BurstTrieMap::new();
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
        let m = BurstTrieMap::new();
        assert!(m.insert("5", 2).is_none());
        assert!(m.insert("2", 9).is_none());
        assert!(!m.insert("2", 11).is_none());
        assert_eq!(m.get("2").unwrap().value(), &11);
    }

    #[test]
    fn test_swap() {
        let m = BurstTrieMap::new();
        assert_eq!(m.insert("1", 2), None);
        assert_eq!(m.insert("1", 3).unwrap().1, 2);
        assert_eq!(m.insert("1", 4).unwrap().1, 3);
    }

    #[test]
    fn test_pop() {
        let m = BurstTrieMap::new();
        m.insert("1", 2);
        assert_eq!(m.remove("1").unwrap().1, 2);
        assert!(m.remove("1").is_none());
    }

    #[test]
    fn test_clear() {
        let m = BurstTrieMap::new();
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
