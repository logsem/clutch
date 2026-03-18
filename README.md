# Clutch-DP Project

This repository contains the Rocq formalization accompanying the PLDI 2026 submission "Modular Verification of Differential Privacy in Probabilistic Higher-Order Separation Logic".

The Clutch-DP logic for differential privacy is built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Rocq prover](https://rocq-prover.org/).

Please refer to [paper_mapping.md](paper_mapping.md) for a detailed table mapping
definitions, rules, and examples from the paper to the Rocq formalization.


## Building the development

The project is known to compile with

- [Rocq](https://rocq-prover.org/) 9.0
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.12.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.4.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.4.4
- [Autosubst](https://github.com/coq-community/autosubst) 1.9
- [Mathcomp](https://github.com/math-comp/math-comp) 2.5.0
- [Mathcomp Analysis](https://github.com/math-comp/analysis) 1.14

The recommended way to install the dependencies locally is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create clutch-dp 4.14.2
opam switch link clutch-dp .
```
3. Add the Rocq `opam` repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```
4. Install the right version of the dependencies as specified in the `rocq-clutch.opam` file.
```
opam install ./rocq-clutch.opam --deps-only
```

You should now be able to build the development by running the command `dune build`.

Note that this command might produce various warnings of the form, which can all be safely ignored:
```
Warning: in file xxx, library
         xxx is required
         from root Coquelicot and has not been found in the loadpath!
         [module-not-found,filesystem,default]
```

## Structure

The formalization is in `theories/diffpriv/`. Key files:

| File | Contents |
|------|----------|
| `diffpriv_rules.v` | DP and sensitivity definitions; composition laws (§2–3) |
| `coupling_rules.v` | `LAPLACE-SHIFT` and `LAPLACE-CHOICE` rules (§3.3) |
| `distance.v` | Distance typeclass and instances (§2.2) |
| `primitive_laws.v` | Heap, tape, and privacy credit resources (§3) |
| `weakestpre.v` | Weakest precondition and coupling modalities (§A.2) |
| `adequacy.v` | Soundness / adequacy theorem (§3, §5, §A.3) |
| `examples/sparse_vector_technique.v` | Above Threshold and Sparse Vector Technique (§4.1) |
| `examples/privacy_filter.v` | Privacy filter and adaptive counting (§4.2) |
| `examples/auto_avg.v` | `auto_avg` client (§4.1.4) |
| `examples/generic_cache.v` | Query cache and `map_cache` client (§4.3) |
| `examples/report_noisy_max.v` | Report Noisy Max (Appendix B) |
| `print_assumptions.v` | Checks axiom dependencies of all main results |

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Rocq's standard library. For example, the following list is produced when executing the command `Print Assumptions all_results.` in [`theories/diffpriv/print_assumptions.v`](theories/diffpriv/print_assumptions.v):

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec :
  ∀ P : nat → Prop,
    (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
PropExtensionality.propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
FunctionalExtensionality.functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g
ClassicalEpsilon.constructive_indefinite_description :
  ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
```
