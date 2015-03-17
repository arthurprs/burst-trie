# BurstTrie
Implements an ordered map as a BurstTrie. It's a very fast Trie variant specialized for Str types.

***This is a work in progress***

This structure achieves better performance than a BTree implementations for common operations while
still allowing range scanning and ordered iteration.

Performance it's usually 50%+ faster than the std lib BTreeMap for random keys (worst case) but it pulls ahead rapdily if keys have common prefixes (See [benchmarks](#benchmarks)).
Memory wise it consumes 90~150% the equivalent BTreeMap. Although on worst case scenarios (uniformelly distributed random keys) it can take up to 300% as much memory as a BTreeMap.

*The Burst Trie was original described by S. Heinz. You can find the original paper in the internet by it's title
"Burst Tries: A Fast, Efficient Data Structure for String Keys"*

### Limitations

It's specialized for string keys, specifically ASCII or UTF-8.

# TODO

* Improve Iterators (reverse versions)
* Improve Range search (reverse and mut versions)
* Set implementation
* Deduplicate some code with macros
* Performance

# Benchmarks

Benchmarks are most of the time pointless. But I figure the only reason to use this over the stdlib BTree implementation is speed. So let's get it over with and find out if it's useless or not.

Note: unless stated as "seq" all benchmarks use uniformelly distributed random keys, which are the worst case scenario for the BurstTrie. Still, the average performance is very good.


| test                                          | ns/iter | Speedup | 
|-----------------------------------------------|---------|---------| 
| map::bench::burst_get_medium_1000             | 186     | 1.909   | 
| map::bench::burst_get_medium_10000            | 270     | 1.985   | 
| map::bench::burst_get_medium_100000           | 599     | 1.810   | 
| map::bench::burst_get_prefix_medium_10000     | 315     | 4.270   | 
| map::bench::burst_get_prefix_medium_100000    | 654     | 3.130   | 
| map::bench::burst_get_seq_100000              | 245     | 4.302   | 
| map::bench::burst_get_short_1000              | 105     | 1.781   | 
| map::bench::burst_get_short_10000             | 156     | 1.859   | 
| map::bench::burst_get_short_100000            | 371     | 1.709   | 
| map::bench::burst_insert_medium_1000          | 242     | 1.760   | 
| map::bench::burst_insert_medium_10000         | 279     | 1.609   | 
| map::bench::burst_insert_medium_100000        | 393     | 1.318   | 
| map::bench::burst_insert_prefix_medium_10000  | 456     | 2.211   | 
| map::bench::burst_insert_prefix_medium_100000 | 615     | 1.792   | 
| map::bench::burst_insert_seq_100000           | 593     | 2.771   | 
| map::bench::burst_insert_short_1000           | 156     | 1.692   | 
| map::bench::burst_insert_short_10000          | 383     | 0.953   | 
| map::bench::burst_insert_short_100000         | 257     | 1.510   | 
| map::bench::burst_iter_10000                  | 111310  | 1.102   | 
| map::bench::burst_range_10000                 | 43580   | 1.416   | 
| map::bench::btree_get_medium_1000             | 355     |         | 
| map::bench::btree_get_medium_10000            | 536     |         | 
| map::bench::btree_get_medium_100000           | 1084    |         | 
| map::bench::btree_get_prefix_medium_10000     | 1345    |         | 
| map::bench::btree_get_prefix_medium_100000    | 2047    |         | 
| map::bench::btree_get_seq_100000              | 1054    |         | 
| map::bench::btree_get_short_1000              | 187     |         | 
| map::bench::btree_get_short_10000             | 290     |         | 
| map::bench::btree_get_short_100000            | 634     |         | 
| map::bench::btree_insert_medium_1000          | 426     |         | 
| map::bench::btree_insert_medium_10000         | 449     |         | 
| map::bench::btree_insert_medium_100000        | 518     |         | 
| map::bench::btree_insert_prefix_medium_10000  | 1008    |         | 
| map::bench::btree_insert_prefix_medium_100000 | 1102    |         | 
| map::bench::btree_insert_seq_100000           | 1643    |         | 
| map::bench::btree_insert_short_1000           | 264     |         | 
| map::bench::btree_insert_short_10000          | 365     |         | 
| map::bench::btree_insert_short_100000         | 388     |         | 
| map::bench::btree_iter_10000                  | 122716  |         | 
| map::bench::btree_range_10000                 | 61714   |         | 


You can of course run it in your computer with ```cargo bench```
