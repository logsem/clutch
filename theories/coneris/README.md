# Summary of examples for the Coneris logic #

We give a brief summary of the more important examples using the Coneris logic. 

## `conTwoAdd` and other variants ##
We have a variety of examples that is similar to the motivating example `conTwoAdd` in the paper. 
The program `conTwoAdd` can be found in [examples/con_two_add.v](examples/con_two_add.v). Though already a simple program, it uses invariants and ghost resources to track all the random sampling and change in the shared location resulting from the fine-grained interleaving between the two parallel threads in order to derive a strict error bound. 

[examples/parallel_add.v](examples/parallel_add.v) is a similar program with slightly similar semantics, in that each threads increment the shared location by 1 with a probability of 2/3. The invariants and ghost resources used is similar.

[examples/two_die.v](examples/two_die.v) is a simpler variant of `conTwoAdd` where there is no shared state between the two threads. Each thread returns the randomly-sampled number, and we add the sum together at the end. Nonetheless, the proof is almost identical since we still need to reason about the change in error credit depending on the order and value produced by the random sampling of the two threads.

## Rand module ##
Consider a module that samples from a uniform distribution in a randomized logical atomic way, what would be a general specification for this. We present a solution in [lib/hocap_rand.v](lib/hocap_rand.v) (also described in the appendix of the Coneris paper). This module exposes presampling tapes, allowing clients to presample values in a logical atomic manner (i.e. we can open invariants temporarily in during the presampling step). Similarly, [lib/hocap_flipv](lib/hocap_flip.v) is a similar module that returns true or false with probability 1/2 each.

In [lib/hocap_rand_atomic.v](lib/hocap_rand_atomic.v), we consider a different specification, where we emphasize that the reading of the tape is performed atomically with a atomic wp. This change gives more flexibility for using the module because one can place the abstract tapes in invariants for the client program. However, there are fewer implementations that satisfy this specification. For example, if we use two `rand 1` to simulate a `rand 3`, this does not satisfy the specification since the randomness is not performed atomically, but across two separate `rand` operations. However, we show that a rejection sampler implementation DOES satisfy this specification even though it may execute arbitrarily many random samplings. This is because the rejection sampler follows a `abort-and-retry` principle, and technically there is only one random operation (the last one) that matters and changes the state of the abstract tape.

(We also mention the somewhat experimental specification in [lib/hocap_rand_alt.v](lib/hocap_rand_alt.v) that also create an exclusive token describing the tape label for the tape allocation operation. This is used in first attempts of the examples written, and we then realize that it is not necessary.)

## Lazy Random Sampler ##
In the appendix, we consider a concurrent lazy one-shot lazy random sampler. The implementation and specification of this can be found in [examples/lazy_rand/lazy_rand_interface.v](examples/lazy_rand/lazy_rand_impl.v), respectively. The `lazyRace` program can be found in [examples/lazy_rand/lazy_rand.v](examples/lazy_rand/lazy_rand_race.v) where we highlight the need to allow presampling to be performed within the `lazyRandf` call.

This lazy random sampler is a client of the random module presented above. 

## Random Counter ##
In the Coneris paper, our first description of a general specification for a concurrent randomized counter module can be found in [examples/random_counter3/](examples/random_counter3/). The specification of `incr_counter` is parametrized with a scary-looking view shift which can be split into two parts: 1. the splitting of the error credits for the random sampling, and 2. the increment of the location by the sampled value. The three implementations can be found in the directory (Note that implementation 2 and 3 requires presampling tapes internally to "compress" the random operations into one randomized logically atomic step to utilize the view shift.) The client program `conTwoAdd` that is modified to utilize the random counter can be found in [examples/random_counter3/client.v](examples/random_counter3/client.v).

To allow more flexible probability reasoning, we provide a even more general specification that **exposes** the presampling tapes as abstract tapes. The specification, implementations, and client code of this version can be found in the [examples/random_counter/](examples/random_counter/) directory. The example `twoIncr` that shows that exposing presampling tapes this way is strictly more expressive can be found in [examples/random_counter/client2.v](examples/random_counter/client2.v).

(We also mention the specification found in [examples/random_counter2/](examples/random_counter2/), which is one of our first attempts of deriving a nice general specification of the random counter module. We soon realize that compared to [examples/random_counter/](examples/random_counter/), this specification is more complicated to use but not more powerful.)

All implementations of the random counter are clients of the abstract rand (or flip) module presented above.

## Hash Module ##
All specifications and implementations of the hash module can be found in [examples/hash/](examples/hash/).

We start by implementing a simple sequential idealized hash function in [examples/hash/con_hash_impl0.v](examples/hash/con_hash_impl0.v) and making it concurrent using a lock. A general specification is defined in [examples/hash/con_hash_interface0.v](examples/hash/con_hash_interface0.v) where we impose no restrictions on what is being sampled by the hash function for each input.

We then consider a more specialized specification for the hash function that distributes errors for each presampling according to whether the value has been sampled before by the hash function. This specification can be found in [examples/hash/con_hash_interface1.v](examples/hash/con_hash_interface1.v), and in [examples/hash/con_hash_impl1.v](examples/hash/con_hash_impl1.v) we show that we can **derive** this specification directly with the specification in [examples/hash/con_hash_interface0.v](examples/hash/con_hash_interface0.v), demonstrating the use of modularity in our proofs.

We go another step further by defining a collision-free concurrent hash [examples/hash/con_hash_interface2.v](examples/hash/con_hash_interface2.v), and we use the previous specification to derive this one, which can be found in [examples/hash/con_hash_impl2.v](examples/hash/con_hash_impl2.v).

Finally, the specification of ultimate concurrent amortized collision-free hash found in the appendix of the Coneris paper is located in [examples/hash/con_hash_interface3.v](examples/hash/con_hash_interface3.v), and we use the previous collision free specification to derive this amortized specification. This proof can be found in [examples/hash/con_hash_impl3.v](examples/hash/con_hash_impl3.v).

In summary, we have a chain of specifications for the hash module, each with increasing specificity, and we show that each specification can be derived from the one in the previous level. Any implementation that satisfies [examples/hash/con_hash_interface0.v](examples/hash/con_hash_interface0.v) hence also satisfies any specification in the higher levels. We also emphasize that the root implementation in [examples/hash/con_hash_interface0.v](examples/hash/con_hash_interface0.v) is a client of the abstract rand module.



The specification in [examples/hash/con_hash_interface4.v](examples/hash/con_hash_interface4.v) corresponds to the thread-safe hash function example in the case studies section of the Coneris paper, and it follows a different story from the chain of hash modules above. Instead of consider the perspective of one abstract tape per client, we change the implementation to fix one abstract tape per **key**. When the hash is initialized, we also create an abstract tape for each possible key. The implementation can be found in [examples/hash/con_hash_impl4.v](examples/hash/con_hash_impl4.v). 

## Bloom Filter ##

We use the thread-safe hash function in [examples/hash/con_hash_interface4.v](examples/hash/con_hash_interface4.v) to implement a concurrent implementation of a Bloom filter. The code can be found in [examples/bloom_filter/concurrent_bloom_filter_alt.v](examples/bloom_filter/concurrent_bloom_filter_alt.v). To the best of our knowledge, we are the **first** to provide a tight bound on the probability of false positives for a concurrent Bloom filter.





