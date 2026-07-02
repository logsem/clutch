# DATA

In this folder you will find a python script which generate random data.
You can execute it with the following  command:
```bash
python gen_data.py
```

## The script

In the current version the script writes in the file `rd_data.csv` a random 
sequence of integers between 0 and 9 with a probability of $\frac{1}{4}$ for 1, 
$\frac{1}{16}$ for 2 and so on (exponential) and stops at 12.

## Other data

Other kind of data can be used.
As the algorithm uses strings as key for the database any file could 
be a database. However the bigger is the domain / the number of different
records in the database / the number of different lines in the file,
the bigger the number of query will be and then the longer it will take.
The execution time is exponential in the size of the domain.

