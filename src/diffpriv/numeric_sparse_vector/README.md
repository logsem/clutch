# Private Multiplicative Weights

In this folder you will find an OCaml implementation of:
- Numeric Sparse Vector technique
- Private Multiplicative Weights

The programs [`main_nsvt.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_nsvt.ml)
and [`main_pmw.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_pmw.ml)
are tests calling the two methods.

## nSVT

The numeric sparse vector technique is an algorithm which given:
- A privacy parameter (`num`, `den`)
- A threshold (`t`)
- The maximum number of numeric answers (`n`)

Outputs a function which given a database (`db`) and a query (`qi`) outputs:
- `None`, if the value returned by the query on the db is under `t` or if it has
        already answered more than `n` numeric values.
- `Some (v)` with `v`$\in \mathbb(Z)$ otherwise.

The `nSVT_stream` is a client which given a stream of queries (represented by a 
function which computes the next query adaptively on the answers) returns the 
list of the answers.

## PMW

The private multiplicative weights is a process which given a database and 
some privacy parameters returns a function which on can call with an adaptive 
stream of queries and get each time a numeric answer.

This algorithm is still in development. We have (for the moment) hardcoded the
threshold and the number of update to the distribution that where allowed.
However it should be computed with the parameters of the function.

For the [`main_pmw.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_pmw.ml)
example, we consider the set of database of $\{ 0,1 \}^k$.
We generate a uniform and a Dirac distribution on this set 
(with [`db_sampling.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/db_sampling.ml).
And we call the algorithm. We print results of the interesting elements of the 
finale distribution.

## NOTES

There have been improvement since last time. Indeed, we don't get a list of $0$
in the output, however it seems to be still incorrect and unpredictable.

We us the probability sampler from [`noiseSampling.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/noiseSampling.ml)
which is a truncated part 
of the file [`../differential_privacy.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/differential_privacy.ml).
