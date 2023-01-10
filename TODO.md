# TODOs and ideas for extensions

- Better rules for working with invariants

- Cleanup couplings rules in Coq development---e.g. specific rules for flip() ~ flip(alpha) are unnecessary

- Tapes with more general sample spaces than just coins

- Epsilon equivalence

- Is having a refCoupl equivalent to having a traditional coupling on the ⊥-lifted relation?

- Could we use the exec_coupl modality instead of the pure-run-ahead in the spec resource algebra to support probabilistic steps on the RHS in isolation?

- Flip-label erasure via tapes_logrel := λ t1 t2 . t1 = t2 = [] instead of t1 = t2.

# Examples

## "Lazy" integer sampling for treap node priorities

## Modeling hash functions
... as if they were perfectly random, then reasoning about hash-based data structures (hash table, bloom filter)

## Modeling hash-based random number generator
One way people implement random number generators, assuming you have a psuedo random function (like a perfect hash, or a cipher like AES) is to have the random number generator keep some private state which is an integer counter. To generate a random number, you increment the counter value and then hash the count and return the result. Assuming we worked out the hashing spec for example 2, we could then go in reverse and show that this hashing based random number generator is contextually equivalent to our flip command.
A more interesting variant would be to do the following. Observe that this RNG is stateful, so to use it in a concurrent setting, you have to protect the counter with a lock or use an fetch and increment, which becomes a bottleneck. Thus for parallel applications, people became interested in "splittable" random number generators, where the API allows you to take a stateful RNG and split it into two RNGs with separate state, where the desired guarantee is that the bits coming from each RNG are independent. 

Famously, Haskell had a very terrible implementation of split which did not even come close to providing this guarantee. Claessen and Palka pointed this bad behavior out and provided a proper implementation of split, where the idea is you partition the key space of counts that the two RNGs are going to use every time you split: https://publications.lib.chalmers.se/records/fulltext/183348/local_183348.pdf

So, it would be pretty cool to show that the "split" operation for us would just refine something that returns two copies of our flip primitive (\lambda _. flip, \lambda _.flip ()). Even if we were not in a concurrent setting, I think this would still be an interesting example to do. 



## Simulate fair coin with unfair coin

## Reservoir sampling

You want to sample k elements from a set of n elements, but you do not know n a priori (imagine you're in a streaming context where you're seeing the set incrementally and you can't revisit an element that you choose not to retain in your sample). One algorithm for doing this is, each time you encounter an element, you assign it a uniform random number from [0, 1], and you keep a running "reservoir" of k elements that have the smallest uniform ID you have seen so far. (This is "Algorithm L" here: https://en.wikipedia.org/wiki/Reservoir_sampling#Optimal:_Algorithm_L). As you see a new element X, you draw its random number, and if it's smaller than any of the elements in the reservoir, you replace the largest element in the reservoir with X. At the end you return the reservoir.
To see why this algorithm is correct, one perspective is to see that this is equivalent to the following non-streaming algorithm: go through the whole set, assigning each a random number in [0, 1]. Then sort the set using the random numbers as the ordering, and then return the first k elements of the sorted array.

We could prove this equivalence as a refinement. The only caveat is that instead of uniform [0,1] random samples, we could instead use a large bounded random integer (say, 128 bits). So there's a small probability of collision, in which case we might return more than k elements. But you could always imagine running it in a loop if you happen to get more than k.

## High level transformation
Can't remember if we've discussed this explicitly, but another nice simple "demo" for our framework is to show that our logical relation validates the equivalence of certain high-level transformations/rewritings that you could imagine a compiler doing: e.g. we can prove
```
let x = flip() in 
let y = f() in
...
is equivalent to

let y = f() in
let x = flip() in 
...
```
for f :  unit -> A

that kind of commuting result has been done for "statistical" probabilistic programming languages in the work of Staton, or with logical relations in that paper with Wand and Culpepper and others, but it's nice that we can do it too in our language (which, while simpler in terms of probabilistic constructs, also has the complexity of state)
