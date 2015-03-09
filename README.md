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

Benchmarks, damm lies, so pointless. But I figure the only reason to use this over the stdlib BTree implementation is speed. So let's get it over with and find out if it's useless or not.

|      |                                               |     |        |      |         |      |      |         | 
|------|-----------------------------------------------|-----|--------|------|---------|------|------|---------| 
| test | map::bench::burst_get_medium_1000             | ... | bench: | 189  | ns/iter | (+/- | 5)   | (1.82x) | 
| test | map::bench::burst_get_medium_10000            | ... | bench: | 275  | ns/iter | (+/- | 20)  | (1.65x) | 
| test | map::bench::burst_get_medium_100000           | ... | bench: | 591  | ns/iter | (+/- | 44)  | (1.62x) | 
| test | map::bench::burst_get_prefix_medium_10000     | ... | bench: | 320  | ns/iter | (+/- | 30)  | (3.53x) | 
| test | map::bench::burst_get_prefix_medium_100000    | ... | bench: | 644  | ns/iter | (+/- | 34)  | (3.12x) | 
| test | map::bench::burst_get_seq_100000              | ... | bench: | 248  | ns/iter | (+/- | 15)  | (4.23x) | 
| test | map::bench::burst_get_short_1000              | ... | bench: | 109  | ns/iter | (+/- | 5)   | (1.73x) | 
| test | map::bench::burst_get_short_10000             | ... | bench: | 156  | ns/iter | (+/- | 15)  | (1.87x) | 
| test | map::bench::burst_get_short_100000            | ... | bench: | 362  | ns/iter | (+/- | 34)  | (1.69x) | 
| test | map::bench::burst_insert_medium_1000          | ... | bench: | 239  | ns/iter | (+/- | 9)   | (1.77x) | 
| test | map::bench::burst_insert_medium_10000         | ... | bench: | 335  | ns/iter | (+/- | 27)  | (1.34x) | 
| test | map::bench::burst_insert_medium_100000        | ... | bench: | 385  | ns/iter | (+/- | 38)  | (1.30x) | 
| test | map::bench::burst_insert_prefix_medium_10000  | ... | bench: | 452  | ns/iter | (+/- | 34)  | (1.98x) | 
| test | map::bench::burst_insert_prefix_medium_100000 | ... | bench: | 595  | ns/iter | (+/- | 51)  | (1.79x) | 
| test | map::bench::burst_insert_seq_100000           | ... | bench: | 604  | ns/iter | (+/- | 59)  | (2.91x) | 
| test | map::bench::burst_insert_short_1000           | ... | bench: | 166  | ns/iter | (+/- | 14)  | (1.71x) | 
| test | map::bench::burst_insert_short_10000          | ... | bench: | 540  | ns/iter | (+/- | 45)  | (0.67x) | 
| test | map::bench::burst_insert_short_100000         | ... | bench: | 257  | ns/iter | (+/- | 58)  | (1.49x) | 
| test | map::bench::btree_get_medium_1000             | ... | bench: | 344  | ns/iter | (+/- | 23)  |         | 
| test | map::bench::btree_get_medium_10000            | ... | bench: | 454  | ns/iter | (+/- | 18)  |         | 
| test | map::bench::btree_get_medium_100000           | ... | bench: | 958  | ns/iter | (+/- | 67)  |         | 
| test | map::bench::btree_get_prefix_medium_10000     | ... | bench: | 1132 | ns/iter | (+/- | 52)  |         | 
| test | map::bench::btree_get_prefix_medium_100000    | ... | bench: | 2010 | ns/iter | (+/- | 163) |         | 
| test | map::bench::btree_get_seq_100000              | ... | bench: | 1051 | ns/iter | (+/- | 39)  |         | 
| test | map::bench::btree_get_short_1000              | ... | bench: | 189  | ns/iter | (+/- | 3)   |         | 
| test | map::bench::btree_get_short_10000             | ... | bench: | 292  | ns/iter | (+/- | 4)   |         | 
| test | map::bench::btree_get_short_100000            | ... | bench: | 613  | ns/iter | (+/- | 40)  |         | 
| test | map::bench::btree_insert_medium_1000          | ... | bench: | 425  | ns/iter | (+/- | 14)  |         | 
| test | map::bench::btree_insert_medium_10000         | ... | bench: | 449  | ns/iter | (+/- | 23)  |         | 
| test | map::bench::btree_insert_medium_100000        | ... | bench: | 504  | ns/iter | (+/- | 31)  |         | 
| test | map::bench::btree_insert_prefix_medium_10000  | ... | bench: | 895  | ns/iter | (+/- | 29)  |         | 
| test | map::bench::btree_insert_prefix_medium_100000 | ... | bench: | 1066 | ns/iter | (+/- | 50)  |         | 
| test | map::bench::btree_insert_seq_100000           | ... | bench: | 1761 | ns/iter | (+/- | 37)  |         | 
| test | map::bench::btree_insert_short_1000           | ... | bench: | 284  | ns/iter | (+/- | 7)   |         | 
| test | map::bench::btree_insert_short_10000          | ... | bench: | 363  | ns/iter | (+/- | 9)   |         | 
| test | map::bench::btree_insert_short_100000         | ... | bench: | 383  | ns/iter | (+/- | 26)  |         | 

You can of course run it in your computer with ```cargo bench```
