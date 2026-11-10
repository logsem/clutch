# Executable semantics for probblaze

A testing and debugging tool for the case studies of
`theories/prob_eff_lang/probblaze`.  It runs the systems of the case
studies, as they are defined in Rocq, against environments written in the
object language, and

* prints execution traces and protocol traces (effects, handlers,
  continuations, samples, and what the environment observes), as text,
  JSON or Mermaid sequence diagrams;
* computes output distributions and advantages exactly, by enumerating
  every outcome of every sampling, when the runs fit a budget, and
  estimates them with confidence intervals by seeded sampling otherwise;
* checks the claims of the case studies on toy instances: correctness of
  honest runs, exact equivalences, and the advantage bounds of the
  security theorems.

```
exec/probblaze-exec list
exec/probblaze-exec run dhke honest real -p 7 --seed 1
exec/probblaze-exec adv dhke dlog real ideal -p 11
exec/probblaze-exec check
```

`probblaze-exec` builds the tool with dune if needed (from the repository
root: `dune build --root . ./exec/src/main.exe`); the first build compiles
the case-study files it extracts from.  `dune build --root .
@exec/src/exec-check` runs `check` on everything.

## How it works

```
exec/theories   Rocq: environments, toy-instance operations (theory clutch_exec)
exec/extract    Rocq extraction of syntax, semantics helpers, systems, environments
exec/src        OCaml: machine, drivers, statistics, traces, registry, CLI
```

**Programs come from Rocq.**  `extract/extract.v` extracts the syntax of
probblaze, the case-study systems (`REAL_DHKE`, `F_AUTH`, `CHAN`, `π_ADD`,
…), the UC operators, and the environments of `theories/`.  The systems
are sections over their class parameters (group, mask, finite types,
schemes), so each becomes an OCaml function of the class records, which
`src/instances.ml` builds for toy groups.  Nothing is transcribed by hand.

**The machine follows `semantics.v`.**  `src/machine.ml` performs one
`prim_step` per call: it refocuses on the next redex and applies the
`head_step` rule, rule by rule.  Substitution, label substitution, frame
filling and the operator evaluations are the extracted Rocq functions.  An
effect is handled by the nearest enclosing handler with its label, which
is where `decomp` stops.  With `--validate`, every step is compared with
the step obtained from the extracted reference decomposition
(`decomp`/`fill`/`to_eff`).  Validation passes on every enumerated run of
`dhke`, `schan`, `dhke-chan`, `add`, `auth` and `ske`, and on sampled runs
of `add3` and `ot-rc`, whose exhaustive validation is too slow.

**Randomness is a choice point.**  `rand` returns a branch to the driver
(`src/explore.ml`), which picks the outcome: from a seed (`--seed S --run
J`: the J-th sampled run of seed S, reproducible), from a list
(`--choices 3,1,4`, then the seed), or all of them with exact rational
probabilities.  Tapes are allocated as in the semantics but never
pre-filled (only the proofs' ghost steps fill them), so sampling from a
tape draws fresh.  Every run prints its choices, so any run can be
replayed.

**Observations.**  An environment is a Rocq function of `obs : string →
val`.  The harness supplies, for each tag, a closure `λ_, ()` and
recognises it by physical identity when it is applied: the call `obs t v`
is recorded as the observation `t v`.  It is an ordinary call of a
function that ignores its argument, so it does not change the output
distribution.

**Traces.**  Events are attributed to an *actor*: `main` (the environment
and the clients it runs), or the handler clause that is running, named by
the effect and its label (`getKey#2`, `send#0`).  The machine keeps
markers in its stack for this; the semantics does not see them.
`--trace view` shows what the environment observes, `proto` adds effects,
resumptions and samples, `exec` adds every step (with the rule of
`base_step`) and heap access.

## Commands

| command | |
|---|---|
| `list` | case studies, their systems, environments, claims and default instances |
| `run CASE ENV SYS` | one run with its trace (`--trace view/proto/exec/none`, `--format text/json/mermaid`, `--seed`, `--run`, `--choices`, `--options` to print sums as `NONE`/`SOME`) |
| `dist CASE ENV SYS` | the output distribution |
| `adv CASE ENV X Y` | the advantage `|Pr[ENV X = true] − Pr[ENV Y = true]|` |
| `diff CASE ENV X Y` | the traces of `ENV X` and `ENV Y` on the same sampling outcomes, as a line diff; `--trace view` compares what the environment sees |
| `check [CASE…]` | every registered claim; exit status 1 if one fails |

The group is chosen with `-g zpx` (the units modulo a prime `p`, order
`p−1`, as in `valgroup_Zpx`) or `-g qr` (the squares modulo a safe prime,
of prime order `(p−1)/2`), and `-p P`.  `dist`, `adv` and `check`
enumerate up to `--max-leaves` runs (default 200 000, `0` forces
sampling) and otherwise sample `--samples` runs (default 10 000), with
Wilson intervals (Newcombe's for differences) at `--confidence` (default
0.99).  `--max-steps` bounds each run.

## Case studies

| case | systems | what `check` tests |
|---|---|---|
| `dhke` | `REAL_DHKE`, `SIM_DHKE ∘f IDEAL_DHKE`, the hybrids with `C_DH_real`/`C_DH_rand`, `DH_KE_tapeless`, the DDH games | honest key agreement; the three exact equivalences of the proof; `adv_DHKE` for a discrete-log distinguisher, whose advantage `1 − 1/|G|` equals that of the DDH reduction |
| `schan` | `REAL_SCHAN`, `SIM_SCHAN ∘f IDEAL_SCHAN` | delivery; perfect security (`adv_SCHAN`) |
| `dhke-chan` | `REAL_DHKE_CHAN`, `SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN`, the DDH games | `dhke_chan_realises`; and that the composed channel never delivers (below) |
| `add` | `REAL_ADD`, `SIM_IDEAL_ADD` | the aggregate is `x · y`; perfect security (`adv_ADD`) |
| `add3` | `REAL_ADD3 c`, `SIM_IDEAL_ADD3 c` for `c = 0, 1, 2` | a scheduler environment that suspends sessions in the network's `wait` (as `scheduler_typed.Zsched`) runs the three parties; all output the product; perfect security (`adv_ADD3`) |
| `auth` | `AUTH`, `AUTH_pad`, `AUTH_ideal`, `S_AUTH ∘f F_AUTH` | delivery; `MAC ≈ MAC_pad`, `AUTH_ideal ≈ S_AUTH ∘f F_AUTH`; `adv_AUTH ≤ 2/q` for a forger whose advantage is `1/q` |
| `ot-rc` | the real and simulated worlds of `adv_ot_rc` | an honest receiver decrypts its message; `adv_ot_rc ≤ 3/n` |
| `ske` | `REAL_SKE`, `SIM_IDEAL_SKE`, `GAME1`, `GAME2`, the encryption oracles, the PRF games, with `PRF_SKE` | delivery; `REAL_SKE ≈ GAME1`, `GAME2 ≈ SIM_IDEAL_SKE`; `adv_SKE` and `adv_schan_prf` for a toy PRF that leaks |

**A finding.**  The secure channel composed with DHKE (`dhke-chan`) never
delivers a message, for any schedule of the client: `CHAN` commits the
message before it asks for Alice's key, and Alice's first key query in
`DH_KE` fails because Bob has not sent his half yet, so the message is
dropped.  The simulator reproduces this, so the security statement holds,
but correctness does not.  With `F_KE_lazy_alice` instead of `DH_KE`
(`schan`), the channel delivers.  See `run dhke-chan honest real`.

`check` runs each case on its default instances (`list` shows them); the
authentication and OT results assume a group of prime order, so those use
`-g qr`.

## Toy instances and what is not proved

* `Zpˣ` uses the extracted operations of `valgroup_Zpx` (the unit and the
  inverse are restated in `theories/zpx_ops.v` and proved equal); its
  `val_group` and generator records are built in OCaml.
* The prime-order subgroup (`theories/qr_ops.v`), the mask `k · m⁻¹`
  (`exec_common.toy_mask`), the finite types `0..n−1` and the PRF
  (`theories/fin_ops.v`) are not proved to satisfy their classes; they
  are test instances.
* `extract.v` realises `fin_val_type.card`, `prod_fvt` and `vg_fvt` on
  descriptors (`extract/exec_fin.ml`) instead of mathcomp structures.
* Composite systems that the case studies define in proof files are
  restated next to their environments (`REAL_DHKE_CHAN`, `SIM_DHKE_CHAN`,
  `RED_DHKE_CHAN`, the real world of `adv_ot_rc`), to keep the extraction
  independent of the proofs.

Not covered: OT with a corrupt sender and the older OT formulations,
`AUTH ∘f DH_KE` (`advantage_auth_dhke.v`), and the eager `F_KE`.

## Adding an environment or a case study

1. Write the environment in `theories/`, as a Rocq function of `obs :
   string → val` over the case study's section parameters
   (`env_dhke.v` is the model).
2. Add it, and any new systems, to the `Extraction` command in
   `extract/extract.v`.
3. Register systems, environments and claims in `src/scenarios.ml`.

Performance: 3 to 6 million steps per second.  `check` on all case
studies takes one to two minutes, most of it enumerating `add3` and
`ot-rc`; with `--validate` it is much slower.
