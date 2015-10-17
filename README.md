# BurstTrie

[![Build Status](https://travis-ci.org/arthurprs/burst-trie.svg)](https://travis-ci.org/arthurprs/burst-trie)

Implements an ordered map as an Adaptive Burst Trie. It's a very fast Trie variant specialized for byte ordered types (like strings).

***This is a work in progress***

This structure achieves better performance than a BTree implementations for common operations while
still allowing range scanning and ordered iteration.

Performance is always better than the std lib BTreeMap and it pulls ahead further if keys have common prefixes (See [benchmarks](#benchmarks)). In some specific cases it's even comparable to a HashMap while keeping the extra functionality of an ordered collections.
Memory wise it consumes 80~100% as much memory as the equivalent BTreeMap/HashMap.

*The Burst Trie was original described by S. Heinz. You can find the original paper in the internet by it's title
"Burst Tries: A Fast, Efficient Data Structure for String Keys"*

#### Limitations

It's specialized for byte ordered keys, like String, &str and &[u8], adapters for other types could be implemented though.

# TODO

- [x] Performance
- [x] Reasonable Memory efficient (could be improved further)
- [ ] Entry API
- [ ] Compile on Rust Stable
- [ ] Iterators
- [ ] Range search
- [ ] Prefix search
- [ ] Set implementation

# Benchmarks

Benchmarks are most of the time pointless. But I figure the only reason to use this over the stdlib BTree implementation is speed. So let's get this over with and find out if it's useless or not.

Note: unless stated as "seq" all benchmarks use uniformelly distributed random keys, which are the worst case scenario for the BurstTrie. Still, the average performance is very good.

```
test map::bench::btree_get_medium_1000             ... bench:         182 ns/iter (+/- 7)
test map::bench::btree_get_medium_10000            ... bench:         292 ns/iter (+/- 13)
test map::bench::btree_get_medium_100000           ... bench:         811 ns/iter (+/- 199)
test map::bench::btree_get_prefix_medium_10000     ... bench:         540 ns/iter (+/- 119)
test map::bench::btree_get_prefix_medium_100000    ... bench:       1,194 ns/iter (+/- 196)
test map::bench::btree_get_seq_100000              ... bench:         333 ns/iter (+/- 40)
test map::bench::btree_get_short_1000              ... bench:         142 ns/iter (+/- 10)
test map::bench::btree_get_short_10000             ... bench:         227 ns/iter (+/- 11)
test map::bench::btree_get_short_100000            ... bench:         543 ns/iter (+/- 278)
test map::bench::btree_insert_medium_1000          ... bench:         267 ns/iter (+/- 27)
test map::bench::btree_insert_medium_10000         ... bench:         378 ns/iter (+/- 123)
test map::bench::btree_insert_medium_100000        ... bench:         490 ns/iter (+/- 89)
test map::bench::btree_insert_prefix_medium_10000  ... bench:         491 ns/iter (+/- 82)
test map::bench::btree_insert_prefix_medium_100000 ... bench:         632 ns/iter (+/- 60)
test map::bench::btree_insert_seq_100000           ... bench:         725 ns/iter (+/- 208)
test map::bench::btree_insert_short_1000           ... bench:         221 ns/iter (+/- 21)
test map::bench::btree_insert_short_10000          ... bench:         332 ns/iter (+/- 52)
test map::bench::btree_insert_short_100000         ... bench:         460 ns/iter (+/- 87)
test map::bench::burst_get_medium_1000             ... bench:         148 ns/iter (+/- 15)
test map::bench::burst_get_medium_10000            ... bench:         172 ns/iter (+/- 79)
test map::bench::burst_get_medium_100000           ... bench:         658 ns/iter (+/- 271)
test map::bench::burst_get_prefix_medium_10000     ... bench:         233 ns/iter (+/- 105)
test map::bench::burst_get_prefix_medium_100000    ... bench:         757 ns/iter (+/- 83)
test map::bench::burst_get_seq_100000              ... bench:         209 ns/iter (+/- 21)
test map::bench::burst_get_short_1000              ... bench:         125 ns/iter (+/- 5)
test map::bench::burst_get_short_10000             ... bench:         140 ns/iter (+/- 12)
test map::bench::burst_get_short_100000            ... bench:         423 ns/iter (+/- 140)
test map::bench::burst_insert_medium_1000          ... bench:         203 ns/iter (+/- 23)
test map::bench::burst_insert_medium_10000         ... bench:         287 ns/iter (+/- 151)
test map::bench::burst_insert_medium_100000        ... bench:         507 ns/iter (+/- 79)
test map::bench::burst_insert_prefix_medium_10000  ... bench:         543 ns/iter (+/- 173)
test map::bench::burst_insert_prefix_medium_100000 ... bench:         666 ns/iter (+/- 61)
test map::bench::burst_insert_seq_100000           ... bench:         498 ns/iter (+/- 68)
test map::bench::burst_insert_short_1000           ... bench:         175 ns/iter (+/- 13)
test map::bench::burst_insert_short_10000          ... bench:         191 ns/iter (+/- 31)
test map::bench::burst_insert_short_100000         ... bench:         365 ns/iter (+/- 108)
test map::bench::hash_get_medium_1000              ... bench:         152 ns/iter (+/- 8)
test map::bench::hash_get_medium_10000             ... bench:         183 ns/iter (+/- 98)
test map::bench::hash_get_medium_100000            ... bench:         425 ns/iter (+/- 25)
test map::bench::hash_get_prefix_medium_10000      ... bench:         192 ns/iter (+/- 12)
test map::bench::hash_get_prefix_medium_100000     ... bench:         455 ns/iter (+/- 27)
test map::bench::hash_get_short_1000               ... bench:         109 ns/iter (+/- 2)
test map::bench::hash_get_short_10000              ... bench:         120 ns/iter (+/- 9)
test map::bench::hash_get_short_100000             ... bench:         264 ns/iter (+/- 30)
test map::bench::hash_insert_medium_1000           ... bench:         186 ns/iter (+/- 13)
test map::bench::hash_insert_medium_10000          ... bench:         271 ns/iter (+/- 35)
test map::bench::hash_insert_medium_100000         ... bench:         446 ns/iter (+/- 62)
test map::bench::hash_insert_prefix_medium_10000   ... bench:         292 ns/iter (+/- 43)
test map::bench::hash_insert_prefix_medium_100000  ... bench:         486 ns/iter (+/- 54)
test map::bench::hash_insert_short_1000            ... bench:         133 ns/iter (+/- 6)
test map::bench::hash_insert_short_10000           ... bench:         170 ns/iter (+/- 4)
test map::bench::hash_insert_short_100000          ... bench:         278 ns/iter (+/- 75)
```

You can of course run it in your computer with ```cargo bench```
