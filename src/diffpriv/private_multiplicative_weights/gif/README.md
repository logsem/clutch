# GIF

In this folder there are files allowing you to build a gif illustration of the 
evolution of the distribution during the `pMW`.

Once you have called `main_pmw.ml` with the call to `oPMW_gif` then you will 
have all the databases that the algorithm whent through in `data/`. 
The 0 database is the real distribution.
In order to get the gif, run:
```bash
python render_gif.py
```
Then it will ask you how many databases where saved, you can get back this number
by reading the `- NB UPDATE : ...` from the output of the `main_pmw.ml`. 

Then it will build the gif.

