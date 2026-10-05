# GIF

In this folder there are files allowing you to build a gif illustration of the 
evolution of the distribution during the `pMW`.

Once you have called `main_pmw.ml` with the argument `--gif` then you will 
have all the databases that the distribution $h$ went through (stored in `data/`). 
The $0^{th}$ database is the real distribution.
In order to get the gif, run:
```bash
python render_gif.py
```
or (if you run before `chmod +x render_gif.py`)
```bash
./render_gif.py
```

The `DB` histogram represents the real database while the `sDB` histogram
represents the sanitized database. It is the one evolving during the process.
I the initial database for `sDB` is the uniforme database then there should not 
have any problem with the axis. However since they are clipped on the values of 
the real database, the histograms might sometimes overpass the view (but it is 
really unlikely)

To do something perfect where the axis are clipped and where everything is in
the view, we should range twice each database to first find the global maximum
and then to build the plots. We prefer clipping the axis based on `DB` which
is fixed and who should be the histogram towards which tends `sDB`.

# Illustration of the issue that comes with the lists implementation

In [`heterogenous_database`](https://github.com/Pbi0/clutch/tree/pMW_formal/src/diffpriv/private_multiplicative_weights/gif/heterogenous_database/)link to the folder you can find several evolutions and the parameters 
associated. It illustrates the issue we encountered with the list 
implementation.

