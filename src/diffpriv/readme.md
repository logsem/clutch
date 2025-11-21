# Differential Privacy in Clutch-DP

This directory contains implementations of differentially private functions.

All references are with respect to the paper "Modular Verification of Differential Privacy in Probabilistic Higher-Order Separation Logic".

The examples roughly follow the structure of this paper.

For all example functions, we provide some concrete inputs to test them.

## From OCaml to RandML: Sampling Noise

The basic sampling primitive we consider is the Laplacian. The function `laplace_discrete scale mean` samples from the discrete Laplacian according to the operational semantics for RandML (see [theories/prob_lang/lang.v](theories/prob_lang/lang.v), Sec.2.3).

The implementation of the Laplacian sampler is based on the Lean formalization of [SampCert](https://github.com/leanprover/SampCert/) but hand-translated to OCaml.

Sometimes it can be instructive to sample from the continuous Laplacian instead of the discrete distribution instead, since this shows more small variations in the output. We provide an implementation of a sampler from the "continuous Laplacian" as a distribution on floating point numbers rather than the reals. This is purely for testing; our proofs have no meaning for this sampler.

We use OCaml's machine integers instead of RandML's unbounded integers. While OCaml supports unbounded integers, machine integers are more user friendly for the sake of this demonstration.

## Sparse Vector Technique

### Above Threshold

The `above_threshold eps t` function interactively evaluates queries until a result exceeding `t` is found.

We prove that the closure `f` returned by `above_threshold eps t` is interactively `eps`-differentially private for clients that only evaluate `f` until the first `true` result is obtained.

### Sparse Vector

The `sparse_vector eps t n` function interactively finds the first `n` queries that exceed `t`.

We prove that the closure `f` returned by `sparse_vector eps t n` is `n*eps`-differentially private for clients that only evaluate `f` until `n` results yielding `true` are obtained.

### Above Threshold Client: `auto_avg`

We implement the `auto_avg` program as a client to `above_threshold` following [Chapter 10, Programming Differential Privacy](https://programming-dp.com/chapter10.html).

We prove that `auto_avg bnds eps db` is `3*eps`-differentially private for any list of bounds `bnds`.

## Privacy Filters

The `mk_filter budget` function implements a privacy filter that can be used to run programs privately such that their total privacy cost is limited to `budget`.

We prove that a client `f` indeed cannot exceed `budget`. We require that the client `f` correctly advertises its privacy cost.

### Privacy Filter Client: Adaptive Count

The `adaptive_count eps_coarse eps_precise threshold budget predicates db` function uses a privacy filter to (privately) count the number of elements in `db` that satisfy the each predicate in `predicates`. If a first coarse count exceeds a `threshold`, a second count with higher privacy budget `eps_precise` is conducted.

## Caching Techniques for DP

## Queries

## Report Noisy Max

The `report_noisy_max eps evalQ n db` function uses `evalQ` to evaluate `n` queries and returns the index of the query that yielded the maximum result.

We prove that `report_noisy_max eps evalQ n db` is `eps`-differentially private if `evalQ k` is 1-sensitive for all indices `k`.
