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
some privacy parameters returns a function which one can call with an adaptive 
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

## DATA

To get the data, you can go to [`data/`](https://github.com/Pbi0/clutch/tree/pMW_formal/src/diffpriv/private_multiplicative_weights/data).

## GIF

If you want to have a gif illustration of the distribution's evolution durring
the pmw, you can modify the call from `oPMW` to `oPMW_gif` and add the argument
`(path_gif ^ file_gif)` in 
[`main_pmw.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_pmw.ml)
and then go to [`gif/`](https://github.com/Pbi0/clutch/tree/pMW_formal/src/diffpriv/private_multiplicative_weights/gif)..
Then you will have in the folder `gif/data/` all the databases that the algorithm
whent through. The 0 database is the real distribution.
In order to get the gif, go in the `gif/` folder and run:
```bash
python render_gif.py
```
Then it will ask you how many databases where saved, you can get back this number
by reading the `- NB UPDATE : ...` from the output of the `main_pmw.ml`. 

Then it will build the gif.



## NOTES

We us the probability sampler from [`noiseSampling.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/noiseSampling.ml)
which is a truncated part 
of the file [`../differential_privacy.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/differential_privacy.ml).
