# ClutchEff Project

## Building the development

The project is known to compile with

- [Rocq](https://rocq-prover.org/) 9.1.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.13.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.5.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.4.4
- [Autosubst](https://github.com/coq-community/autosubst) dev
- [Mathcomp](https://github.com/math-comp/math-comp) 2.5.0
- [Mathcomp Analysis](https://github.com/math-comp/analysis) 1.14

The recommended way to install the dependencies locally is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new project-local switch.
```
opam switch create . --empty
```
3. Add the Rocq `opam` repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `rocq-clutch.opam` file.
```
opam install ./rocq-clutch.opam --deps-only
```

You should now be able to build the development by using `dune build`.

## Overview

The development lives in [`theories/prob_eff_lang/probblaze`](theories/prob_eff_lang/probblaze); paths below are relative to that directory.
Several directories have their own README with a file-by-file description; they are linked below.

### Language

| File | Contents |
|---|---|
| `syntax.v` | Expressions, values, frames and evaluation contexts: a lambda calculus with references, presampling tapes and `rand`, effect names (`Effect s e`), `Do`, and handlers (`Handle`) that are deep or shallow and one-shot (`OS`) or multi-shot (`MS`). |
| `semantics.v` | The probabilistic head-step relation, evaluation contexts, label neutrality (`NeutralEctx`), and the instance `blaze_prob_lang` of Clutch's `language`. |
| `notation.v` | Derived forms (`let:`, `match:`, `handle:`, destructuring `let,`) and notation for programs. |
| `class_instances.v` | `Atomic` and `PureExec` instances. |
| `metatheory.v` | Deterministic and probabilistic head steps, tape updates, and `rand`/`rand` couplings. |
| `erasure.v` | Erasure of tape presampling: a program with sampled tapes has the same output distribution as without. |

### Program logic

| File | Contents |
|---|---|
| `primitive_laws.v` | Ghost state for heap, tapes and labels (`probblazeGS`), points-to and tape assertions, and weakest-precondition rules for the primitives. |
| `spec_ra.v`, `spec_rules.v` | Resources for the specification (right-hand) program and the rules for stepping it. |
| `ectx_lifting.v` | Lifting lemmas for head steps. |
| `coupling_rules.v` | Coupling rules between `rand` and tapes on the two sides: along bijections and injections, avoiding a list of values, fragmented, and between labelled tapes. |
| `wp_adequacy.v` | Adequacy of the weakest precondition with error credits. |
| `logic.v` | The relational logic: relational theories (`iThy`, sums, the one-shot operator), the refinement judgement `REL e1 ≤ e2 <\|X\|> {{R}}`, its labelled version `BREL e1 ≤ e2 <\|L\|> {{R}}`, and their rules for pure steps, state, effects and handlers, probabilistic couplings and invariants. |
| `pure_weakestpre.v` | `PREL`, a relation for pure programs, and its embedding into `BREL`. |
| `adequacy.v` | Soundness of `REL` and `BREL`: a refinement yields an (approximate) coupling of the output distributions (`brel_refines_coupling`). |
| `proofmode.v`, `tactics.v`, `spec_tactics.v` | Proof-mode classes and tactics for `BREL`/`REL` (`brel_pures_l`, `brel_load_r`, …) and for stepping the specification program. |

### Semantic type system

| File | Contents |
|---|---|
| `sem_def.v` | Semantic types (binary value relations), persistently monotonic protocols, semantic signatures and rows, environments. |
| `mode.v` | Modes (`OS`, `MS`), their lattice, and mode/type and mode/environment subsumption. |
| `sem_sig.v` | Effect signatures `⟨op1, op2⟩ : κ ⇒ ι` and the flip-bang `¡[m] σ`. |
| `sem_row.v` | Rows (`⟨⟩`, `σ · ρ`, `¡[m] ρ`, union) and row subtyping. |
| `sem_types.v` | Type formers: base types, tapes, (copyable and substructural) references, products, sums, effectful arrows `τ -{ρ}-∘ κ`, the bang `![m] τ`, polymorphism over types, rows and modes, existentials, recursive types. |
| `sem_env.v` | Environments, their splitting and subtyping. |
| `sem_operators.v` | Typing of unary and binary operators. |
| `sem_judgement.v` | The semantic typing judgement `Γ₁ ⊨ e1 ≤ e2 : ρ : τ ⫤ Γ₂` and its value variant `⊨ᵥ v1 ≤ v2 : τ`. |
| `compatibility.v` | Compatibility lemmas: one semantic typing rule per language construct, plus subsumption and tactics for typing proofs. |

### Syntactic type system ([`typing/`](theories/prob_eff_lang/probblaze/typing))

| File | Contents |
|---|---|
| `types.v` | Syntax of types, rows and signatures, contexts, and the syntactic typing judgment. |
| `interp.v` | Interpretation of syntactic types into semantic types and the binary logical relation. |
| `fundamental_subtyping.v` | Syntactic subtyping is sound for the interpretation. |
| `compatibility_interp.v` | The compatibility lemmas at interpreted types. |
| `fundamental.v` | The fundamental theorem. |

### Equivalence logic ([`eq/`](theories/prob_eff_lang/probblaze/eq))

A judgement `EQ el ≈ er` that proves both refinements `BREL el ≤ er` and `BREL er ≤ el` with one proof script: `eq_logic.v` (the judgement and its rules), `eq_handlers.v` (effects and handlers), `eq_compat.v` (rules from semantic typing), `eq_valgroup.v` and `eq_finval.v` (groups and finite value types).
See [`eq/README.md`](theories/prob_eff_lang/probblaze/eq/README.md).

### Composition ([`uc/`](theories/prob_eff_lang/probblaze/uc))

| File               | Contents                                                                                                                                            |
|--------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------|
| `advantage.v`      | The advantage of an environment against two programs, and theorems bounding it from semantic typing and from `BREL` refinements with error credits. |
| `uc_advantage.v`   | Advantage under an evaluation context (the basis for reductions), and zero advantage from a two-sided relation.                                     |
| `comp_operators.v` | Session types `τ__F`, `τ__f` and the composition operators.                                                                                         |
| `uc_systems.v`     | Systems as factories (`fac m τ`) and the operators lifted to factories (`∘f`, `\|\|ᵣ`, `∘F`).                                                       |
| `uc_theorem.v`     | The composition theorem `uc_composition`.                                                                                                           |
| `uc_typed.v`       | From syntactically typed environments to the semantic environments of the advantage bounds.                                                         |


The design is explained in [`uc/DESIGN.md`](theories/prob_eff_lang/probblaze/uc/DESIGN.md).

### Examples ([`examples/`](theories/prob_eff_lang/probblaze/examples))

Infrastructure for the cryptographic examples:

| Directory | Contents |
|---|---|
| `valgroup/` | Groups on values (`val_group`, `clutch_group`) with closed, typed implementations of the operations (`valgroup.v`), the instance `ℤₚˣ` (`valgroup_Zpx.v`), and groups as finite value types (`valgroup_finval.v`). |
| `fin_val_type/` | Finite value types (`fin_val`) with coding to and from integers (`fin_val_type.v`) and their products (`fin_val_type_prod.v`). |
| `ske/ske.v` | Abstract symmetric encryption (`SYM`), the real/ideal encryption oracles and the one-time secrecy games. |
| `otp/otp.v` | The one-time pad over a group as an instance of `SYM`. |

Case studies, each with its own README:

| Directory | Contents |
|---|---|
| [`prf/`](theories/prob_eff_lang/probblaze/examples/prf/README.md) | Encryption from a pseudorandom function, and the secure-channel results instantiated with it. |
| [`auth/`](theories/prob_eff_lang/probblaze/examples/auth/README.md) | An authenticated channel from one-time MACs. |
| [`dhke/`](theories/prob_eff_lang/probblaze/examples/dhke/README.md) | Diffie–Hellman key exchange over an authenticated channel, reduced to DDH. |
| [`secure_channel/`](theories/prob_eff_lang/probblaze/examples/secure_channel/README.md) | One-message secure channels (by one-time pad and by symmetric encryption), and their composition with DHKE. |
| [`secure_add/`](theories/prob_eff_lang/probblaze/examples/secure_add/README.md) | Secure addition with a corrupt aggregator. |
| [`secure_add3/`](theories/prob_eff_lang/probblaze/examples/secure_add3/README.md) | Three-party secure addition with one passively corrupted party; the multi-session example. |
| `ot/` | DDH-based oblivious transfer with a common reference string, for a corrupt receiver (`OT_Rcorrupt_thunk.v`, `definition_thunk_receiver_corrupt.v`) and a corrupt sender (`OT_SCorrupt_thunk.v`, `definition_thunk_sender_corrupt.v`); shared resources and theories in `ot_common.v`, couplings in `ot_bijection.v`, and the advantage bounds `adv_ot_rc` and `adv_ot_final` in `advantage_ot.v`. |


## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Rocq's standard library. For example, the following list is produced when executing the command `print_assumptions.v` in [`theories/prob_eff_lang/probblaze/print_assumptions.v`](theories/prob_eff_lang/probblaze/print_assumptions.v), printing the assumptions for `uc_composition`:

```
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec :
  forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  {n : nat | ~ P n} + {forall n : nat, P n}
PropExtensionality.propositional_extensionality :
  forall P Q : Prop, P <-> Q -> P = Q
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
ClassicalEpsilon.constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

