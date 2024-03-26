import random

MAX = 10000

d = dict()
# def hashstr(s, d = dict()):
def hashstr(s):
    h = d.get(s)
    if h is None:
        h = random.randint(0, MAX)
        d[s] = h
    return h

# Find the first occurance of p in s.
def rk(s, p):
    lp = len(p)
    hp = hashstr(p)
    for i in range(len(s) - lp + 1) :
        w = s[i : i+lp]
        h = hashstr(w)
        if h == hp :
            if w == p :
                return i
    return -1

# Check if s and t have any shared substrings of length k.
def rkl(s, t, k):
    ds = dict()
    dt = dict()
    for i in range(len(s) - k + 1) :
        w = s[i : i+k]
        h = hashstr(w)
        ds[h] = i
    for j in range(len(t) - k + 1) :
        w = t[j : j+k]
        h = hashstr(w)
        i = ds.get(h)
        if not (i is None) :
            return ((i, s[i : i+k]), (j, t[j : j+k]))
    return None

# Find the longest common substring of s and t.
def rkmax(s, t):
    mn, mx = 1, min(len(s), len(t))
    r = None
    while lim > 0 and mn <= mx :
        k = int((mn + mx) / 2)
        x = rkl(s, t, k)
        if x is None :
            mx = k - 1
        else :
            mn = k + 1
            r = x
    return r
