# BurstTrie

[![Build Status](https://travis-ci.org/arthurprs/burst-trie.svg)](https://travis-ci.org/arthurprs/burst-trie)

Implements an ordered map as an Adaptive Burst Trie. It's a very fast Trie variant specialized for byte ordered types (like a string).

***This is a work in progress***

This structure achieves better performance than a BTree implementations for common operations while
still allowing range scanning and ordered iteration.

Performance is usually better than the std lib BTreeMap for random keys (worst case) but it pulls ahead further if keys have common prefixes (See [benchmarks](#benchmarks)).
Memory wise it consumes 90~140% memory of the equivalent BTreeMap.

*The Burst Trie was original described by S. Heinz. You can find the original paper in the internet by it's title
"Burst Tries: A Fast, Efficient Data Structure for String Keys"*

### Limitations

It's specialized for byte ordered keys, like String, &str and &[u8].

# TODO

* Entry API
* Compile on Rust Stable
* Improve Iterators (reverse versions)
* Improve Range search (reverse and mut versions)
* Set implementation
* Deduplicate some code with macros
* Performance

# Benchmarks

Benchmarks are most of the time pointless. But I figure the only reason to use this over the stdlib BTree implementation is speed. So let's get this over with and find out if it's useless or not.

Note: unless stated as "seq" all benchmarks use uniformelly distributed random keys, which are the worst case scenario for the BurstTrie. Still, the average performance is very good.


| test                                          | ns/iter | Speedup | 
|-----------------------------------------------|---------|---------| 
| map::bench::burst_get_medium_1000             | 218    | 1.20x | 
| map::bench::burst_get_medium_10000            | 261    | 1.40x | 
| map::bench::burst_get_medium_100000           | 680    | 1.26x | 
| map::bench::burst_get_prefix_medium_10000     | 452    | 1.84x | 
| map::bench::burst_get_prefix_medium_100000    | 853    | 1.99x | 
| map::bench::burst_get_seq_100000              | 410    | 1.73x | 
| map::bench::burst_get_short_1000              | 140    | 1.07x | 
| map::bench::burst_get_short_10000             | 164    | 1.52x | 
| map::bench::burst_get_short_100000            | 463    | 1.25x | 
| map::bench::burst_insert_medium_1000          | 284    | 1.21x | 
| map::bench::burst_insert_medium_10000         | 356    | 1.23x | 
| map::bench::burst_insert_medium_100000        | 548    | 0.95x | 
| map::bench::burst_insert_prefix_medium_10000  | 669    | 1.15x | 
| map::bench::burst_insert_prefix_medium_100000 | 841    | 1.03x | 
| map::bench::burst_insert_seq_100000           | 682    | 1.72x | 
| map::bench::burst_insert_short_1000           | 186    | 1.28x | 
| map::bench::burst_insert_short_10000          | 242    | 1.40x | 
| map::bench::burst_insert_short_100000         | 364    | 1.14x | 
| map::bench::burst_iter_10000                  | 124874 | 1.01x | 
| map::bench::burst_range_10000                 | 51707  | 1.30x | 
| map::bench::btree_get_medium_1000             | 262    |       | 
| map::bench::btree_get_medium_10000            | 367    |       | 
| map::bench::btree_get_medium_100000           | 857    |       | 
| map::bench::btree_get_prefix_medium_10000     | 833    |       | 
| map::bench::btree_get_prefix_medium_100000    | 1704   |       | 
| map::bench::btree_get_seq_100000              | 710    |       | 
| map::bench::btree_get_short_1000              | 151    |       | 
| map::bench::btree_get_short_10000             | 250    |       | 
| map::bench::btree_get_short_100000            | 581    |       | 
| map::bench::btree_insert_medium_1000          | 345    |       | 
| map::bench::btree_insert_medium_10000         | 441    |       | 
| map::bench::btree_insert_medium_100000        | 526    |       | 
| map::bench::btree_insert_prefix_medium_10000  | 772    |       | 
| map::bench::btree_insert_prefix_medium_100000 | 872    |       | 
| map::bench::btree_insert_seq_100000           | 1176   |       | 
| map::bench::btree_insert_short_1000           | 239    |       | 
| map::bench::btree_insert_short_10000          | 339    |       | 
| map::bench::btree_insert_short_100000         | 417    |       | 
| map::bench::btree_iter_10000                  | 126224 |       | 
| map::bench::btree_range_10000                 | 67495  |       | 



You can of course run it in your computer with ```cargo bench```
