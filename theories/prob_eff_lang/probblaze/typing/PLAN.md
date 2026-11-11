# Syntactic type checker for probblaze: hand-off plan

Branch `prob_eff_lang-tychk` (three commits ahead of `prob_eff_lang`).
Everything below refers to files under
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
  send handler, four files in `examples/secure_channel/`; commit `47ff68d0`).
  No other instance exists.
* Copyable references move to non-atomic invariants (section 1) and get
  syntactic typing rules in the first stage (section 2).
* The driver is written in Ltac1 with typeclasses, matching the rest of
  probblaze (Ltac2 is only used under `theories/approxis/`).
* `τ__F` (`uc/comp_operators.v:42`) takes its client unrestrictedly since
  commit `09e8cb48` (`⊸` became `→`). Every `τ__F`-shaped syntactic mirror
  (`T_SCHAN`, `T_DHKE`, `T_ADD`, `T_DHKE_CHAN`, `T_SKE`, `T_DHKE_SKE`) now has
  `⇾` as its outer arrow and its `*_subtype` proof carries a
  `ty_le_mbang_comp` step. The same commit deleted `τ__Fu`, `τ__Fu_le_τ__F`,
  `EtaT`, `sem_oval_typed_eta`, `τ_DH_OS`, `τ_CHAN_OS`, `τsc_OS` and the
  `*_typed_u` wrappers; do not look for them.

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
   `le.MultiT` is transported by `multi_ty_sound`
   (`fundamental_subtyping.v:426`), `ρ R⪯T τ` by `row_type_sub_sound` (`:481`;
   its context sibling is `row_env_sub_sound`, `:496`), as in the `App_typed`
   case of `fundamental.v` (`:218`).
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
Structural rules: base types, `TBang`, products, sums, `TRefC`, type and
row quantifiers (via `TBangTForallTComm{1,2}_le` and
`TBangTForallRComm{1,2}_le`); `RNil_le_ctx` and `RRefl_le` exist in the
derived-rules section of `types.v`. Mode quantifiers have no bang rule, so
`le.MultiT (∀M: τ)` is a residual goal (follow-up, section 10). Abstract types supplied by classes
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
Transitivity is the constructor `le.RTrans_le`.

The second lemma of the pair needs the converses of the flip rules, because
`RFlipCons_le` and `RFlipUnion_le` only push a flip inward and the one-shot
case cannot be derived. They were added on 2026-11-10 as `RFlipConsInv_le`
and `RFlipUnionInv_le` (sound by reflexivity: both sides denote the same
semantic row; `row_le_RFlipConsInv`, `row_le_RFlipUnionInv` in
`fundamental_subtyping.v`). The converse of `RFlipNil_le` is an instance of
`RFlipIntro_le`. A probe (`probe_tychk_row.v` at the repository root, not
committed) has `norm_row`, `denorm`, both round-trip lemmas for all rows,
and a first `row_le_solve`, all without admits. Its known limits:
signatures are matched syntactically (no `≤S`), no `RErase_le`, and no
contraction, so `{σ, σ} ≤ {σ}` fails.

C4. One derived lemma per constructor in algorithmic form (inputs: `Δ`,
`Γ1`, `e`, `ρ`; outputs: `τ` and `Γ2`, or `τ` checked). Points to get right:

* Right-to-left evaluation: `App_typed`, `BinOp_typed`, `Pair_typed`,
  `StoreC_typed` thread the context through the right operand first.
* `App_typed` has rows `ρ'`, `ρ''` and a flag `b`; instantiate both rows to
  `ρ` with `RRefl_le`, flag `true` (the existing proofs end with
  `Unshelve. all: first [exact true | exact OS]`; mode evars appear as well,
  except in `Zsched_typed`, which passes every argument explicitly).
* `App_typed` wants a bare `TArrow` (`-{ ρ'' }-∘`) in function position,
  while `Rec_typed` and the notations `⇾`, `-{ ρ }->`, `-{ ρ }-[ m ]->`
  produce `TBang m (TArrow …)` (`types.v:812-817`). Every application of a
  lambda-typed value therefore goes through `Sub_typed` with `TBangElim_le`
  (`:1116`).
* Variables: consume (`typed_var_at`) by default; copy (`typed_var_bang`)
  when the entry is `MultiT` and used again. Deciding "used again" needs the
  free variables of the rest of the expression; a simpler first version
  always copies `MultiT` entries and weakens leftovers at the end.
* Binders (`Let_typed`, `Match_typed`, `LetPair_typed`, `TUnpack`,
  handlers, `Rec_typed`): drop every same-named entry from the context after
  the bound expression (that is the only derivation available, see section 8).
* `Rec_typed`: the split `Γ ;; Γ'` is computed from the free variables of
  the body; `BAnon` needs `m m⪯C Γ`, a named function needs `le.MultiC Γ`;
  the body must end with the empty context. `Rec_pure_typed` puts `x` at the
  head and `f` below it, the reverse of `Rec_typed`.
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
and no hand derivation. They live in five files: `Zsched_typed`
(`examples/secure_add3/scheduler_typed.v:140`), `vexp_typed`
(`examples/valgroup/valgroup.v:109`), the seven instance lemmas of
`examples/valgroup/valgroup_Zpx.v` (`vunit_p_typed`, `vmult_p_typed`,
`vinv_p_typed`, `veq_p_typed`, `int_of_vg_p_typed`, `vg_of_int_p_typed`,
`vgval_p_typed`), `int_of_prod_typed`, `prod_of_int_typed` and
`fvtval_prod_typed` (`examples/fin_val_type/fin_val_type_prod.v`), and
`sample_typed` and `DH_real_typed` (`examples/dhke/dhke_common.v`). There is
no derivation of `mask_typed`: it is a field of `Class Mask`
(`examples/secure_channel/mask.v:8`) that no instance proves.

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
(`examples/secure_channel/advantage_sec_channel.v:81`) whose body calls through
row variables; such bodies are typeable only since `RBot_le`. Since
`09e8cb48` the outer arrow of `T_SCHAN` is `⇾`, so a value at that interface
is a `TBang MS` function: `Rec_typed` at mode `MS`, which needs
`MS m⪯C Γ` on the captured context.

## 5. Stage E: bridge to the semantic interfaces

A checker result reaches the semantic world through `fundamental` /
`fundamental_val` at an interpreted syntactic type, while the downstream
theorems want the semantic interface types (`chan`, `gk`, `τ__F`, `fac`, the
session types of `uc/uc_systems.v` and `uc/comp_operators.v`). Already
present: `typed_env_fac` (`uc/uc_typed.v:28`) and hand-written mirrors with
subtype lemmas: `T_SCHAN` (`advantage_sec_channel.v:81`, subtype `:89`),
`T_DHKE` (`dhke/advantage_dhke.v:416`), `T_ADD`
(`secure_add/advantage_secure_add.v:37`), `T_ADD3`
(`secure_add3/advantage_add3.v:32`), `T_DHKE_CHAN`
(`advantage_dhke_sec_channel.v:141`), `T_SKE`
(`advantage_ske_sec_chan.v:260`), `T_DHKE_SKE`
(`advantage_dhke_ske_sec_chan.v:565`), `T_rc` and `T_sc`
(`ot/advantage_ot.v:46`, `:324`). All but `T_rc`/`T_sc` are `τ__F`-shaped
and since `09e8cb48` use `⇾`, with a `ty_le_mbang_comp` / `mode_le_refl`
step in their subtype proofs.

* A central simp set of interpretation unfolding lemmas (`interp._ty` on
  `TArrow`, `TBang`, `TProd`, `TSum`, `TForallR`, `TRefC`, …). The only
  existing ones are `interp_TArrow` and `interp_TBang` in
  `examples/ot/advantage_ot.v:12-16` (plain lemmas by `reflexivity`, unused);
  nothing exists for the other constructors.
* A structural subtyping tactic that proves the `*_subtype` lemmas: they are
  twenty lines of `ty_le_row_forall` (`sem_types.v:429`), `ty_le_arr`
  (`:370`), `ty_le_prod` (`:394`), `ty_le_sum` (`:405`), `ty_le_mbang_comp`
  (`:670`) with leaves such as `τG_subtype` (a field of `Class clutch_group`,
  `examples/valgroup/valgroup.v:178`).
* Syntactic mirrors for the remaining interface types.

Status (2026-11-10, uncommitted): done except new mirrors.
* `typing/interp_simp.v`: one `reflexivity` equation per constructor of
  `vmode`, `type`, `row`, `eff_sig`, plus `!!!` on a cons and `interp._env`
  on nil/cons; rewrite database and tactic `interp_simp` (does not go under
  binders). The two lemmas in `advantage_ot.v` are left alone.
* `typing/bridge.v`: `sem_ty_le_struct [using leaf]` proves
  `τsem ≤ₜ interp._ty η μ δ T ξ` (either direction). It unfolds the mirror's
  head, rewrites with `interp_simp`, and decomposes along whichever side is a
  semantic former. Rows close by `row_le_refl`, modes by `mode_le_refl`,
  `mode_le_MS` or `mode_le_OS`, and leaves by `ty_le_refl` or `leaf`. `leaf`
  is tried on `A ≤ₜ B` and then after `iIntros (??) "!#"`. Unclosed goals are
  left to the user. Every `iApply` is followed by `solve_constraints`: a
  postponed unification failure otherwise escapes `first`/`try`.
* All seven `*_subtype` proofs (`T_SCHAN`, `T_DHKE`, `T_ADD`, `T_ADD3`,
  `T_DHKE_CHAN`, `T_SKE`, `T_DHKE_SKE`) are now one `sem_ty_le_struct` call.
  The leaf is `iApply τG_subtype` and/or the two pinned `τFT_subtype`. Each
  file gained the import `From clutch.prob_eff_lang.probblaze.typing Require
  Import bridge.`. Only the six standard axioms are used.
* Mirrors: none added, because no target needs one. Instances of `τ__F`,
  `τ__f`, `hdl` and `fac` are expressible per instance; the operators
  themselves are not (no type-level λ). With `τG`/`τFT` as the leaf,
  `leakI` has an exact mirror. `gk` and `cli` have one only for
  `τ ≤ ⟦T⟧`, and `aleak` and `oaleak` only for `⟦T⟧ ≤ τ`. `chan` and
  `τ_ENC` have none in either direction, because `𝔾` and `Msg` are only
  below `⟦τG⟧` and `⟦τFT⟧` (section 6). With a `TVar` instantiated to
  `𝔾` they would all be exact. `τ_sl` and `pure_ty` have no counterpart.

## 6. Stage F: end-to-end conversion

Re-prove `oauth_send_handler_typed` (`examples/secure_channel/sec_channel_typing.v:84`)
as a syntactic derivation found by `tychk`, transported by `fundamental` and
the bridge; the semantic lemma becomes a corollary. This exercises copyable
references, `Option` payloads with the sum bang rule, a one-shot continuation
under a flipped row, and the renamed binder. Then the DH handler,
`dh_handler_typed` (`examples/dhke/dhke_typing.v:864`). Programs that must
stay semantic: anything using `τ_sl` (ideal channel and simulator; defined in
`sec_channel_ideal_typing.v:46` and again in
`advantage_dhke_ske_sec_chan.v:100`), `pure_ty` (`auth/auth_prf.v:192`), and
the relational escape lemmas (`sem_typed_of_brel3` `auth_prf.v:54`,
`sem_typed_select` `auth_typing.v:393`, `sem_typed_sample2`
`auth_typing.v:95`).

Row bound (decided 2026-11-10, option A). Both handler lemmas assume
`(¡ θ) ≤ᵣ ρh`, which the syntactic judgement cannot express. They are
restated with the explicit row `sem_row_union (¡ θ) ρ` (syntactic mirror
`¡[OS] RVar 1 ∪ᵣ RVar 0`); each caller proves both inclusions between its
handler row and that union with `row_le_submseteq`. The top-level typing
statements do not change.

Group type (open; decide when Stage F starts). Findings of 2026-11-10:
* The authenticated channel never inspects what it stores: the send handler
  stores and leaks `m`, the receive handler returns `!message`.
* Proving the handlers at `⟦τG⟧` instead of `𝔾` does not suffice. Only
  `𝔾 ⊆ ⟦τG⟧` holds (`τG_subtype`; for Zpx `τG := TInt`). F_OAUTH would then
  hand `⟦τG⟧` values to CHAN, whose receive handler masks them
  (`sem_typed_mask` needs `𝔾`; the SKE version decrypts and needs `Cph`),
  and `uc_composition` forces F_OAUTH and CHAN to share one interface type.
  The header comment of `sec_channel_typing.v` ("𝔾 = ⟦τG⟧") is wrong.
* What works: derive the handler at a type variable, written `![MS] (TVar 0)`
  so the payload is copyable, and instantiate the variable with `𝔾` (or `Cph`
  for the SKE copy); `fundamental` holds for every type environment. Since
  `𝔾` is pure, `![MS] 𝔾` and `𝔾` are equivalent, and `Refᶜ` respects
  equivalence (`sem_ty_ref_cpy_proper`).
* The DH handler computes `g^"a"` inline; exponentiation is only typed at
  `τG`, so the type-variable route does not apply to it as is.

Decision (2026-11-10): option 1. The two send handlers (`sec_channel_typing.v`
and the SKE copy in `ske_sec_chan_typing.v`) are derived syntactically at a
type variable `![MS] (TVar 0)` and instantiated with `𝔾` / `Cph`. The DH
handler `dh_handler_typed` stays semantic for now. Options for it later:
pass `g` and exponentiation to the handler as context variables (changes the
DH program), or add opaque base types with certified values to the typing
layer (large change).

## 7. Policies and gotchas

* Shadowing: rename the inner binder (or use `<>` when unused). To find
  offending programs, look for non-empty set-aside frames in uses of
  `sem_typed_match_split` and for `sem_typed_frame_env_gen` around a binder.
* The repository is `/workspace/projects/clutch`; run `dune` from there,
  with `DUNE_BUILD_DIR=/home/node/build` (set in the environment). Build per
  file: `dune build theories/…/foo.vo`.
* `rocq-mcp` needs the imported `.vo` files in
  `/home/node/build/default/theories`; `_CoqProject` must map that directory
  to `clutch` (`_CoqProject.container` has the right content; the committed
  `_CoqProject` points at `_build/`). dune produces no `.vos` files and
  deletes touched markers on every build, so after each build run
  `find /home/node/build/default -name "*.vo" | while read f; do [ -f "${f%.vo}.vos" ] || touch "${f%.vo}.vos"; done`
  and then restart the session. Heavy example files should be loaded by
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

## 10. Follow-ups

* Bang rule for mode quantifiers. `le._type` has bang commutation rules for
  type and row quantifiers but none for `TForallM`, so `le.MultiT (∀M: τ)`
  is not derivable structurally. Add `TBangTForallMComm1_le` and
  `TBangTForallMComm2_le` next to the row-quantifier pair; they are sound by
  `ty_le_mode_forall_mbang` and `ty_le_mbang_mode_forall`
  (`sem_types.v:796`, `:788`). Unlike the type and row cases, the bang's
  mode must be shifted when it moves under the binder, because `vmode` has
  variables (`MVar`): the rule is `TBang m (TForallM α) ≤ TForallM (TBang
  m.[ren (+1)] α)` and its converse. Soundness then also needs the
  interpretation fact that a shifted mode ignores the new head of `μ`. The
  soundness cases in `fundamental_subtyping.v` are positional bullets, so
  insert them at the matching position. Not needed yet: no file under `examples/` or `uc/` uses
  a mode quantifier (checked 2026-11-10).

## 11. Status (2026-11-10, uncommitted)

* Stage A done: `Refᶜ` is on `na_invP` (`sem_types.v`), the three `*_cpy`
  lemmas use `brel_na_*`, `ref_cpy_alloc` uses `na_inv_alloc`.
* Stage B done: `TRefC`, `refᶜ`, `TBangRefC_le`, `AllocC_typed`,
  `LoadC_typed`, `StoreC_typed`, interpretation, soundness, wrappers
  `interp_c_*_refc`, three cases in `fundamental`; hand derivation in
  `typing/tests.v`. `fundamental` uses only the six standard axioms.
* C3 rules: `RFlipConsInv_le`, `RFlipUnionInv_le` added (sound by
  reflexivity).
* Stage C and D done in `typing/tychk.v`: side-predicate hints, context
  operations, row normaliser and `row_le_solve` (with `≤S` matching,
  erasure and `once_solve`), algorithmic lemmas for every judgement, and the
  driver `tychk` with the wrappers `tyann` and `sigann`. `typing/tychk_tests.v`
  re-proves every syntactic lemma of the five example files with `tychk`
  alone (the scheduler needs three annotations) plus an adversary at a
  `T_SCHAN`-shaped interface. The original example proofs are unchanged.
* Stage F preparation: option A for the row bound is applied (the two send
  handlers and the DH handler are stated at `sem_row_union (¡ θ) ρ`; callers
  use `clause_at_union_row` from `compatibility.v`). Top-level statements
  are unchanged.
* Build: every probblaze file builds with `dune build -j 1` and
  `OCAMLRUNPARAM=o=20`, except that `examples/ot/OT_Rcorrupt_thunk.v` and
  `OT_SCorrupt_thunk.v` are OOM-killed whenever anything else runs; build
  them alone with `OCAMLRUNPARAM=o=10`.
* Stage E done except new mirrors (none needed yet): `typing/interp_simp.v`
  (unfolding equations, rewrite database `interp_simp`) and `typing/bridge.v`
  (tactic `sem_ty_le_struct`). The seven `*_subtype` lemmas of the
  advantage files are now one tactic call each; each of those files gained
  one `Require Import` of `bridge`. See section 5 for the mirror analysis.
* `examples/ot/OT_SCorrupt_thunk.v` and `advantage_ot.v` could not be
  rebuilt here (OOM even alone with `o=10`); they are not otherwise affected.
* Stage F, option 1, done for the send handler: `typing/stagef.v` has
  `oauth_send_handler_syn` (`tychk` alone, one `tyann` giving the leak call
  the row `¡[OS] (RVar 1)`, else `RVar 1 R⪯C Γ` is left) and its corollary
  `oauth_send_handler_sem` at any `MultiT τ` (via `fundamental`, `[τ]`,
  `[ρ; θ₂]`, `![MS] τ ≡ τ`). Both `oauth_send_handler_typed` are one
  `iApply` of it, with `𝔾` / `Cph`; six standard axioms only.
* Next: the DH handler (section 6).
