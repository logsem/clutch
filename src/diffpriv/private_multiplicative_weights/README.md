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
function which computes the next query adaptively to the answers) returns the 
list of the answers.

## PMW

The private multiplicative weights is a mechanism which given a database and 
some privacy parameters returns a function which one can call with an adaptive 
stream of queries and get each time a numeric answer.

This algorithm is working. There is just a point to raise.
The implementation is derived from C.Dwork book on differential privacy (!!!cite better),
in which the threshold is computed in order to match an accuracy statement.
Since we are working on small databases, the threshold often get really high. 
Then very few updates are made and the execution is not interesting.
Then we can lower manually the threshold to get an interesting output.
Even if it does change something about the accuracy statement, it do
not change anything for the privacy one. 
That is why we are making this choice. Then the threshold will need 
to be modified depending on the database under study.

For the [`main_pmw.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_pmw.ml)
example, we consider the database that are randomly generated  [`rd_data.csv`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/data/rd_data.csv)
.
Or the databases from ... (!!!push and cite the database.)

In order to manage the databases and histograms we uses functions defined in 
[`db_query.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/db_query.ml).

When calling:
```bash
ocaml main_pmw.ml
```

The output is, the initial database and the approached (sanitized) database as well 
as the list of the distances between the real answer and the returned answer 
to the stream of queries.

You can add the two optional following arguments:
- `--gif` in order to save the databases in a folder
- `--file [file]` in order to specify the database to use
- `--list` use the list implementation.

For the `--list` option, instead of using the hastable implementation, it uses
lists. It is the translation of what is written in rocq into ocaml.
It then uses a natural (int) distribution / it is not normalized.

## DATA

To get the data, you can go to [`data/`](https://github.com/Pbi0/clutch/tree/pMW_formal/src/diffpriv/private_multiplicative_weights/data).

## GIF

If you want to have a gif illustration of the distribution evolution during
the pmw, you can add the argument `--gif` when calling
[`main_pmw.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/main_pmw.ml)
and then can go to [`gif/`](https://github.com/Pbi0/clutch/tree/pMW_formal/src/diffpriv/private_multiplicative_weights/gif)
where you will find in the folder `gif/data/` all the distribution that $h$
went through. The 0 database is the real distribution.
In order to get the gif, go in the `gif/` folder and run:
```bash
python render_gif.py
```
or 
```bash
./render_gif.py
```

It will build the gif under the name of `evolution_distrib.gif`.

![Evolution of the distribution.](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/private_multiplicative_weights/gif/evolution_distrib.gif?raw=true "Evolution of the distribution.")

## NOTES

We use the probability sampler from [`noiseSampling.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/numeric_sparse_vector/noiseSampling.ml)
which is a truncated part 
of the file [`../differential_privacy.ml`](https://github.com/Pbi0/clutch/blob/pMW_formal/src/diffpriv/differential_privacy.ml).
