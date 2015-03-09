# BurstTrie
Implements an ordered map as a BurstTrie. It's a very fast Trie variant specialized for Str types.

***This is a work in progress***

This structure achieves better performance than a BTree implementations for common operations while
still allowing range scanning and ordered iteration. Performance wise it's usually 50+% faster than
the std lib BTreeMap for random keys but it pulls ahead rapdily if keys have common prefixes.

It's specialized for string keys, specifically ASCII or UTF-8.

*The Burst Trie was original described by S. Heinz. You can find the original paper in the internet by it's title
"Burst Tries: A Fast, Efficient Data Structure for String Keys"*

# TODO

It's a fairly long list right now

* Iterators
* Index
* Range search
* More tests
* Set implementation
* Performance


# Benchmarks

Benchmarks,  so pointless. But I figure the only reason to use this over the stdlib BTree implementation is speed. So let's get it over with and find out if it's useless or not.

|                                               |      |         |         | 
|-----------------------------------------------|------|---------|---------| 
| map::bench::burst_get_medium_1000             | 189  | ns/iter | (1.82x) | 
| map::bench::burst_get_medium_10000            | 275  | ns/iter | (1.65x) | 
| map::bench::burst_get_medium_100000           | 591  | ns/iter | (1.62x) | 
| map::bench::burst_get_prefix_medium_10000     | 320  | ns/iter | (3.53x) | 
| map::bench::burst_get_prefix_medium_100000    | 644  | ns/iter | (3.12x) | 
| map::bench::burst_get_seq_100000              | 248  | ns/iter | (4.23x) | 
| map::bench::burst_get_short_1000              | 109  | ns/iter | (1.73x) | 
| map::bench::burst_get_short_10000             | 156  | ns/iter | (1.87x) | 
| map::bench::burst_get_short_100000            | 362  | ns/iter | (1.69x) | 
| map::bench::burst_insert_medium_1000          | 239  | ns/iter | (1.77x) | 
| map::bench::burst_insert_medium_10000         | 335  | ns/iter | (1.34x) | 
| map::bench::burst_insert_medium_100000        | 385  | ns/iter | (1.30x) | 
| map::bench::burst_insert_prefix_medium_10000  | 452  | ns/iter | (1.98x) | 
| map::bench::burst_insert_prefix_medium_100000 | 595  | ns/iter | (1.79x) | 
| map::bench::burst_insert_seq_100000           | 604  | ns/iter | (2.91x) | 
| map::bench::burst_insert_short_1000           | 166  | ns/iter | (1.71x) | 
| map::bench::burst_insert_short_10000          | 540  | ns/iter | (0.67x) | 
| map::bench::burst_insert_short_100000         | 257  | ns/iter | (1.49x) | 
| map::bench::btree_get_medium_1000             | 344  | ns/iter |         | 
| map::bench::btree_get_medium_10000            | 454  | ns/iter |         | 
| map::bench::btree_get_medium_100000           | 958  | ns/iter |         | 
| map::bench::btree_get_prefix_medium_10000     | 1132 | ns/iter |         | 
| map::bench::btree_get_prefix_medium_100000    | 2010 | ns/iter |         | 
| map::bench::btree_get_seq_100000              | 1051 | ns/iter |         | 
| map::bench::btree_get_short_1000              | 189  | ns/iter |         | 
| map::bench::btree_get_short_10000             | 292  | ns/iter |         | 
| map::bench::btree_get_short_100000            | 613  | ns/iter |         | 
| map::bench::btree_insert_medium_1000          | 425  | ns/iter |         | 
| map::bench::btree_insert_medium_10000         | 449  | ns/iter |         | 
| map::bench::btree_insert_medium_100000        | 504  | ns/iter |         | 
| map::bench::btree_insert_prefix_medium_10000  | 895  | ns/iter |         | 
| map::bench::btree_insert_prefix_medium_100000 | 1066 | ns/iter |         | 
| map::bench::btree_insert_seq_100000           | 1761 | ns/iter |         | 
| map::bench::btree_insert_short_1000           | 284  | ns/iter |         | 
| map::bench::btree_insert_short_10000          | 363  | ns/iter |         | 
| map::bench::btree_insert_short_100000         | 383  | ns/iter |         | 

You can of course run it in your computer with ```cargo bench```
