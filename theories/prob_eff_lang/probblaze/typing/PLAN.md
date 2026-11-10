# Syntactic type checker for probblaze: hand-off plan

Branch `prob_eff_lang`. Everything below refers to files under
`theories/prob_eff_lang/probblaze/` unless a path says otherwise.

## 0. Goal and context

Programs in the examples are typed in two ways: syntactically, with the
inductive judgement `typed` in `typing/types.v` and the fundamental lemma
`fundamental` in `typing/fundamental.v`, or semantically, by composing the
compatibility lemmas of `compatibility.v` by hand. Syntactic derivations are
written by hand today (e.g. `examples/secure_add3/scheduler_typed.v`). The
semantic derivations are long (about 3500 lines across the `*_typing.v`
files) and most of them contain no relational reasoning, so they are
candidates for a checker.

The goal is an Ltac1 tactic that, given a concrete expression, an input
context and a row, builds the `typed` derivation, leaving a small, predictable
set of residual goals where annotations are needed. The approach is
bidirectional: the row and the input context are inputs, the type is
synthesised or checked, the output context is computed. Subtyping is used only
at coercion points (variables, values, application). Reflection (a computable
checker plus a soundness proof) is a possible later stage; the tactic comes
first because it reuses the existing rules directly.

Decisions already taken:

* The declarative system has been extended (commits `c9bdba0e..140f730f`):
  row bottom `RBot_le`, union laws (`RUnionComm_le`, `RUnionAssoc{1,2}_le`,
  `RUnionNil{Left,Right}{1,2}_le`, `RUnionCons{1,2}_le`), bang distribution
  over sums and products in both directions, and the function rule
  `Rec_typed` / `Rec_pure_typed` now lets an anonymous one-shot lambda capture
  affine variables (`BAnon` needs `m m⪯C Γ`; a named recursive function still
  needs `le.MultiC Γ`). All soundness cases are closed.
* Shadowing. Every binder rule carries `x ∉ ctx_dom Γ2 → x ∉ ctx_dom Γ3`. A
  binder that shadows an entry which must survive it cannot be typed. The fix
  (a frame slot per binder rule, see section 8) is shelved. Until then,
  programs are changed so that no binder shadows a live entry. One instance
  was renamed (`SOME "message"` became `SOME "stored"` in the authenticated
  send handler, four files in `examples/secure_channel/`; compiled, not yet
  committed at the time of writing). No other instance exists.
* Copyable references move to non-atomic invariants (section 1) and get
  syntactic typing rules in the first stage (section 2).
* The driver is written in Ltac1 with typeclasses, matching the rest of
  probblaze (Ltac2 is only used under `theories/approxis/`).

## 1. Stage A: copyable references on non-atomic invariants

Why: the current model `sem_ty_ref_cpy` (`sem_types.v:37`, notation `Refᶜ`)
wraps both points-to assertions and the payload relation in an atomic Iris
`inv` (namespace `tyN.@(l1,l2)`). The contents are available for one atomic
step only, so `sem_typed_load_cpy` needs a persistent payload (`MultiT τ`) and
no rule can take an affine payload out and put another in. The relational
judgement already threads a non-atomic token (`na_ownP`, `logic.v:416`), and
`brel` has `brel_na_alloc` (`logic.v:3694`), `brel_na_inv` (`:3704`) and
`brel_na_close` (`:3716`). Moving the model to `na_invP` keeps every current
rule and later allows a non-atomic "replace" rule.

Changes:

1. `sem_types.v:37`: `inv (tyN.@(l1,l2)) P` becomes `na_invP (tyN.@(l1,l2)) P`.
   `na_invP` needs `probblazeRGS Σ`; the definition currently takes
   `probblazeGS Σ`. Change the class and check every section that mentions the
   type (the sections of `sem_types.v` already assume `probblazeRGS`; check
   `typing/interp.v`). Persistence is unchanged, so
   `ty_le_mbang_intro_ref_cpy` (`:575`) and `multi_ty_ref_cpy` (`:582`) should
   go through as they are.
2. `compatibility.v`, three lemmas, keeping their statements:
   * `sem_typed_alloc_cpy` (`:1230`): replace `rel_inv_alloc` by
     `brel_na_alloc`.
   * `sem_typed_load_cpy` (`:1248`): replace the `brel_atomic_l` /
     `inv_acc` / `step_load` / `wp_load` block by: `brel_na_inv` with
     `E := ⊤`, `N := tyN.@(l1,l2)`; destruct the `▷ ∃ w1 w2, …` (values are
     inhabited); `brel_load_l` (`logic.v:2969`, takes `▷ l1 ↦ v1`, its
     continuation is under `▷`, so `iNext` strips the remaining laters);
     `brel_load_r` (`:2980`); `brel_na_close` with the invariant body
     re-established; `brel_value`. The payload copy still needs `MultiT τ`.
   * `sem_typed_store_cpy_gen` (`:1284`): same skeleton with `brel_store_l`
     (`:2991`) and `brel_store_r` (`:3002`), closing with the new value and
     its payload proof.
   The linear-reference lemmas `sem_typed_load_expr` and
   `sem_typed_store_expr`, directly below, are the same step sequences
   without an invariant and serve as templates.
3. `examples/auth/advantage_auth.v:36` (`ref_cpy_alloc`) allocates the
   invariant by hand with `inv_alloc`; switch to `na_inv_alloc`. This is the
   only site outside `sem_types.v` and `compatibility.v` that unfolds the
   model (checked by grepping for `tyN`, `sem_ty_ref_cpy` and `inv_acc`).
4. The tape type `sem_ty_tape` (`sem_types.v:31`) stays on the atomic `inv`;
   out of scope.

Future rule enabled by this stage (not part of this plan): a "replace" rule
for the non-atomic sequence load-then-store on one reference, typed under a
single opening of the invariant, with no `MultiT` requirement on the payload.

Acceptance: `compatibility.v`, `advantage_auth.v` and all example files that
use `Refᶜ` compile (the examples only go through the three lemmas, so they
should not need changes). No admits.

## 2. Stage B: syntactic copyable references

Nothing exists syntactically. `TRef` is the affine, typestate reference:
`TAlloc`, `TLoad` on a variable (`ref τ` becomes `ref ⊤`), `TStore` on a
variable (`types.v:1425-1431`), covariant `TRef_le`, interpreted by
`sem_ty_ref` (`interp.v:53`). The semantic corpus never uses it; it uses
`Refᶜ` 83 times (49 loads, 30 stores, 27 allocations).

Add, in this order:

1. `types.v`: constructor `TRefC : type → type` (next to `TRef`, `:49`), a
   case in each of the substitution and renaming fixpoints that mention
   `TRef` (`hsubst_vmode_type` `:121`, `rename_type` `:202`, the row
   renaming's type case `:261`, `subst_type` `:283`, the row substitution's
   type case `:336`) and in the effect-name collector `_ty` (`:1277`), plus a
   notation `refᶜ τ` beside `ref τ` (`:834`).
2. Subtyping in `le._type`:
   * `TBangRefC_le D m α : _type D (TRefC α) (TBang m (TRefC α))`, sound by
     `ty_le_mbang_intro_ref_cpy`. This makes `le.MultiT (TRefC τ)` derivable.
   * Optional, only if a target needs it: invariance
     `_type D α β → _type D β α → _type D (TRefC α) (TRefC β)`, sound via
     `na_inv_iff`. The corpus never subtypes under `Refᶜ`.
3. Typing rules in `typed`, on expressions, same evaluation order as the
   semantic lemmas (right operand first):

   ```
   AllocC_typed : Γ1 ⊢ e : ρ : τ ⊣ Γ2  →  Γ1 ⊢ ref e : ρ : refᶜ τ ⊣ Γ2
   LoadC_typed  : le.MultiT τ → Γ1 ⊢ e : ρ : refᶜ τ ⊣ Γ2  →  Γ1 ⊢ ! e : ρ : τ ⊣ Γ2
   StoreC_typed : ρ R⪯T τ → Γ2 ⊢ e1 : ρ : refᶜ τ ⊣ Γ3 → Γ1 ⊢ e2 : ρ : τ ⊣ Γ2
                  →  Γ1 ⊢ e1 <- e2 : ρ : () ⊣ Γ3
   ```

   `ref e` is `AllocN #1 e` for both reference kinds (`notation.v:33`,
   `:127`), so `TAlloc` and `AllocC_typed` apply to the same syntax; the
   checker decides by the expected type and defaults to copyable (section 4).
4. `interp.v:53`: case `TRefC τ ↦ sem_ty_ref_cpy (…)`.
5. `fundamental_subtyping.v`: case for `TBangRefC_le` (and invariance if
   added).
6. `compatibility_interp.v`: wrappers `interp_c_alloc_refc`,
   `interp_c_load_refc`, `interp_c_store_refc`, following
   `interp_c_alloc_ref` (`:519`) and using the three `*_cpy` lemmas;
   `le.MultiT` is transported by `multi_ty_sound`, `ρ R⪯T τ` by the
   row-type-sub soundness lemma used in the `App_typed` case.
7. `fundamental.v:133`: three new cases.
8. A hand-written test derivation (new file `typing/tests.v`, or inside the
   file of the first target) for
   `let: "r" := ref NONE in match: !"r" with NONE => "r" <- SOME v | SOME x => … end`
   to confirm the rules are usable before any automation exists.

Acceptance: `fundamental.v` compiles with no admits; the test derivation
compiles.

## 3. Stage C: algorithmic layer (new file `typing/tychk.v`)

Precedent for the shape of the file: `theories/prob_lang/typing/tychk.v`.
Reusable material already in `examples/secure_add3/scheduler_typed.v`:
`solve_fresh`, `once_nil`, `erase_absent` (decides `D !! s` by
`vm_compute`), `typed_perm`, `typed_perm_out`, `typed_row_cons`,
`typed_val_row`, `typed_var_dup`, `typed_var_bang`, `typed_var_at`,
`typed_call`. Generalise these and move them into `typing/`.

C1. Side predicates as typeclass goals (`Hint Extern` or instances):
`le.MultiT`, `le.MultiC`, `m m⪯C Γ`, `ρ R⪯T τ`, `ρ R⪯C Γ`, `le.OnceR`.
Structural rules: base types, `TBang`, products, sums, `TRefC`, quantified
types (via the bang-comm rules); `RNil_le_ctx` and `RRefl_le` exist in the
derived-rules section of `types.v`. Abstract types supplied by classes
(`τG_multi` in `examples/valgroup/valgroup.v:61`, `τFT_multi` in
`examples/fin_val_type/fin_val_type.v:31`) are registered as hints in their
files. Anything else is a residual goal.

C2. Context operations: lookup by name returning the position, delete,
bring-to-front. The lemmas go through `Sub_typed` with `CRefl_le`,
`_ctx_perm_left`, `_ctx_perm_right`, `CTrans_le`. Note the shapes:
`ctx_insert` prepends, `Var_typed` consumes the head, and `le._ctx` is a
fixpoint whose clauses are existentials over a `pre ++ (x,t') :: post` split.

C3. Row subtyping decision. Normal form of a row: a multiset of signatures
(flips pushed onto signatures with `RFlipCons_le`, `RFlipUnion_le`,
`RFlipNil_le`) plus a set of row-variable atoms (`RVar i`, `RFlip m (RVar i)`).
One lemma pair `ρ ≤R norm ρ` and `norm ρ ≤R ρ` at every flag `b`, proved
from the union laws, `RExtend_le`, `RSwap_le`, `RRefl_le`. A tactic
`row_le_solve` for `D ⊢ₗ ρ' ≤R ρ @ b`: normalise both sides, then inclusion
of normal forms (`RBot_le` for the empty source, `RExtend_le`/`RSwap_le` for
signatures, `RVar_le` for atoms, `RUnion_le` congruence). Erasure
(`RErase_le`) only at `b = true` and only for `SAbs` signatures, discharged
with `erase_absent`. Note `RUnion_le` takes its premises at `b = false`.

C4. One derived lemma per constructor in algorithmic form (inputs: `Δ`,
`Γ1`, `e`, `ρ`; outputs: `τ` and `Γ2`, or `τ` checked). Points to get right:

* Right-to-left evaluation: `App_typed`, `BinOp_typed`, `Pair_typed`,
  `StoreC_typed` thread the context through the right operand first.
* `App_typed` has rows `ρ'`, `ρ''` and a flag `b`; instantiate both rows to
  `ρ` with `RRefl_le`, flag `true` (the existing proofs end with
  `Unshelve. all: exact true`).
* Variables: consume (`typed_var_at`) by default; copy (`typed_var_bang`)
  when the entry is `MultiT` and used again. Deciding "used again" needs the
  free variables of the rest of the expression; a simpler first version
  always copies `MultiT` entries and weakens leftovers at the end.
* Binders (`Let_typed`, `Match_typed`, `LetPair_typed`, `TUnpack`,
  handlers, `Rec_typed`): drop every same-named entry from the context after
  the bound expression (that is the only derivation available, see section 8).
* `Rec_typed`: the split `Γ ;; Γ'` is computed from the free variables of
  the body; `BAnon` needs `m m⪯C Γ`, a named function needs `le.MultiC Γ`;
  the body must end with the empty context.
* Values: `Val_typed` gives row `RNil`; coerce with `Sub_typed` and
  `RBot_le`. Literal naturals are `LitV (LitInt n)` with `n : nat`, and
  `TNat_le_TInt` relates the two numeric types.
* `TAlloc` versus `AllocC_typed`: by expected type, default copyable.
* Quantifier elimination (`TAbsElim_typed`, `RAbsElim_typed`,
  `MAbsElim_typed`): instantiate by matching against the expected type; if
  the expected type does not fix the instance, leave a hole or read an
  annotation (section 4).
* Effects and handlers: `Effect_typed` extends `Δ`; `Do_typed` and the two
  handler rules need the signature and the handlee's type, which come from
  the expected row or an annotation.

Acceptance: the existing syntactic lemmas re-proved with the derived lemmas
and no hand derivation, in particular `Zsched_typed`
(`examples/secure_add3/scheduler_typed.v`), `vexp_typed`
(`examples/valgroup/valgroup_Zpx.v`), the lemmas of
`examples/fin_val_type/fin_val_type_prod.v`, `sample_typed` and
`DH_real_typed` (`examples/dhke/dhke_common.v`), `mask_typed`
(`examples/secure_channel/mask.v`).

## 4. Stage D: the driver tactic

`tychk`: on a goal `Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2` with `Γ1`, `e`, `ρ` concrete
and `τ`, `Γ2` either concrete or evars, `lazymatch` on `e`, apply the derived
lemma of C4, recurse, discharge freshness with `solve_fresh`, and push side
conditions to the C1 hints. Residual goals must have one of these shapes:
`le.MultiT τ` for an abstract type, `D ⊢ₗ τ' ≤T τ` or `D ⊢ₗ ρ' ≤R ρ @ b`
that `row_le_solve` could not close, `⊢ᵥ v : τ` for an opaque value, and an
instantiation hole.

Annotations are definitional identity wrappers, so theorem statements keep
the plain expression:

```
Definition tyann   (_ : type) (e : expr) : expr := e.           (* e at type τ *)
Definition rowinst (_ : row)  (e : expr) : expr := e.           (* ∀R instance *)
Definition sigann  (_ : eff_name) (_ _ : type) (e : expr) : expr := e.  (* handled signature *)
```

with notations on top. The tactic reads them before any `simpl`; `simpl`
removes them. Needed at: let-bound lambdas, `ref NONE` allocations (payload
type), handler signatures, and row instantiations the expected type does not
fix. Add a wrapper only when a target needs it.

Targets: `Zsched_typed` as regression, and one adversary-shaped value at a
syntactic interface such as `T_SCHAN`
(`examples/secure_channel/advantage_sec_channel.v`) whose body calls through
row variables; such bodies are typeable only since `RBot_le`.

## 5. Stage E: bridge to the semantic interfaces

A checker result reaches the semantic world through `fundamental` /
`fundamental_val` at an interpreted syntactic type, while the downstream
theorems want the semantic interface types (`chan`, `gk`, `τ__F`, `fac`, the
session types of `uc/uc_systems.v` and `uc/comp_operators.v`). Already
present: `typed_env_fac` (`uc/uc_typed.v`) and hand-written mirrors with
subtype lemmas (`T_SCHAN_subtype` in `advantage_sec_channel.v`, `T_DH`,
`T_ADD`, `T_ADD3`, `T_rc`, `T_sc`).

* A central simp set of interpretation unfolding lemmas (`interp._ty` on
  `TArrow`, `TBang`, `TProd`, `TSum`, `TForallR`, `TRefC`, …); the ones in
  `examples/ot/advantage_ot.v` are currently local.
* A structural subtyping tactic that proves the `*_subtype` lemmas: they are
  twenty lines of `ty_le_row_forall`, `ty_le_arr`, `ty_le_prod`,
  `ty_le_sum`, `ty_le_mbang_comp` with leaves such as `τG_subtype`.
* Syntactic mirrors for the remaining interface types.

## 6. Stage F: end-to-end conversion

Re-prove `oauth_send_handler_typed` (`examples/secure_channel/sec_channel_typing.v:84`)
as a syntactic derivation found by `tychk`, transported by `fundamental` and
the bridge; the semantic lemma becomes a corollary. This exercises copyable
references, `Option` payloads with the sum bang rule, a one-shot continuation
under a flipped row, and the renamed binder. Then the DH handler
(`examples/dhke/dhke_typing.v`). Programs that must stay semantic: anything
using `τ_sl` (ideal channel and simulator), `pure_ty` (authentication), and
the relational escape lemmas (`sem_typed_of_brel3`, `select`, `sample2`).

## 7. Policies and gotchas

* Shadowing: rename the inner binder (or use `<>` when unused). To find
  offending programs, look for non-empty set-aside frames in uses of
  `sem_typed_match_split` and for `sem_typed_frame_env_gen` around a binder.
* `dune` must run from `/workspace/clutch-eff` with `--root .`; the parent
  directory contains other dune projects with the same package name. Build
  per file: `dune build --root . theories/…/foo.vo`.
* `rocq-mcp` needs the imported `.vo` files built in
  `_build/default/theories`; `_CoqProject` maps that directory to `clutch`.
  Restart the session after a build. Heavy example files should be loaded by
  incremental imports rather than one preamble.
* Flags on row subtyping: `RUnion_le` premises at `false`; erasure only at
  `true`. The disjointness context is `le.row_to_disj_ctx ρ` of the ambient
  row; `update_disj_ctx` on arrows.
* `Match_typed`, `Let_typed`, `LetPair_typed`, `TUnpack` and the handler
  rules carry freshness premises on both the intermediate and the output
  context; `solve_fresh` discharges them for concrete contexts.
* `Nat_val_typed` applies to `LitV (LitInt n)` with `n : nat` coerced to `Z`;
  `vm_compute` may be needed to see the coercion.
* `RRefl_le`, `CRefl_le`, `CTrans_le`, `_ctx_perm_left/right`, `RNil_le_ctx`
  are in the derived-rules section at the end of `types.v`.

## 8. Shelved: frame slots on binder rules

Design, for later. Each sequential binder rule gets a frame `Γs` with
`ρ R⪯C Γs`: the context after the bound expression splits as `Γs ;; Γ2'`,
the body runs on `Γ2'` with the binder, the output is `Γs ;; Γ3'`, the
freshness premises mention `Γ2'` and `Γ3'` only. Syntax-directed, one slot per
rule, no general frame rule. The existing rules are the instance `Γs = []`,
so they can be replaced rather than duplicated. Soundness: `Match_typed` by
`sem_typed_match_split` (`compatibility.v:777`, with the explanatory comment
above it); `Let_typed`, `LetPair_typed`, `TUnpack` need split variants, each a
copy of that proof. The handler return clause can take the same slot but its
proof is not a copy. `Rec_typed` already has its frame `Γ'`. In the checker,
the derived lemma for a binder then partitions the context by binder name
instead of dropping.

## 9. Order and checklist

1. Stage A, non-atomic `Refᶜ`: model, three lemmas, one example site. Build
   `compatibility.v` and every file using `Refᶜ`.
2. Stage B, syntactic `TRefC`: types, interpretation, subtyping case, three
   rules, three wrappers, three fundamental cases, test derivation.
3. Stage C, algorithmic layer: side-predicate hints, context operations, row
   normaliser and `row_le_solve`, derived lemmas; regression on the five
   existing syntactic lemma files.
4. Stage D, driver: `tychk`, wrappers as needed; scheduler and one adversary.
5. Stage E, bridge: simp set, structural subtyping tactic, mirrors.
6. Stage F, end to end: `oauth_send_handler_typed`, then the DH handler.

Each stage ends with no admits and a per-file build of everything it
touched. Do not start a stage on an unbuilt predecessor.
