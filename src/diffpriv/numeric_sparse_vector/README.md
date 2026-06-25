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

This algorithm is still in development. The only issue remaning is one with the 
threshold (it is too high hence each ansewrs are under the threshold).

For the [`main_pmw.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_pmw.ml)
example, we consider the database that was randomly generated  [`rd_data.csv`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/data/rd_data.csv)
.

In order to manage the databases and histograms we uses functions defined in 
[`db_query.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/db_query.ml).

When calling:
```bash
ocaml main_pmw.ml
```

The output is, the initial database and the output (sanitized) database as well 
as the list of the distances between the real answer and the returned answer 
to the stream of queries.

## NOTES

We us the probability sampler from [`noiseSampling.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/noiseSampling.ml)
which is a truncated part 
of the file [`../differential_privacy.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/differential_privacy.ml).
