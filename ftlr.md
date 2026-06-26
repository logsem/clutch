# Fundamental Theorem of the Logical Relation (`probblaze`) — status report

**Target.** `Theorem fundamental` (+ mutual `fundamental_val` / `fundamental_pure`) in
`theories/prob_eff_lang/probblaze/typing/fundamental.v`: every syntactically
well-typed term is semantically related to itself
(`Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2  →  ⊢ 〈Δ;Γ1〉 ⊨ₜ e ≤log≤ e : ρ : τ ⫤ Γ2`), and
analogously for values and the pure fragment.

**Headline.** Of the **53 cases** (32 typing + 11 value + 10 pure), **46 are
discharged**. The 7 open cases (`App`, `Sub`, `Effect`, `Do`, `DeepHandle`,
`ShallowHandle`, `TRand`) are all blocked on the *same small set* of core
semantic-judgement / model changes, for which the supporting infrastructure is
already built. Along the way the central `sem_sig_later` model blocker was
resolved, the type-substitution machinery was made capture-avoiding, and ~11
genuine soundness bugs in the (work-in-progress) type system were found and
fixed. Baseline commit: `0d8b5d5b` (builds clean; 19 commits this effort).

---

## 1. What is proved (46/53)

**Typing judgement — 25/32.** Var, Val, Pure, Pair, Fst, Snd, InjL, InjR,
Match, If, Rec, TAbsElim, RAbsElim, MAbsElim, TAlloc, TLoad, TStore, TAllocTape,
TRandU, TFold, TUnfold, TPack, TUnpack, Contraction, Weakening.

**Value judgement — 11/11.** Unit, Int, Nat, Bool, Pair, InjL, InjR, Rec,
TAbs, RAbs, MAbs.

**Pure judgement — 10/10.** Val, Rec, Pair, InjL, InjR, Var, BangIntro, TAbs,
RAbs, MAbs.

A handful of these (Contraction, BangIntro_pure, Pair_pure, and the Pair/TStore
typing cases) are *discharged* — i.e. contain no `admit` — but transitively rest
on one sharp foundational admit, `le_multiT_MultiP_topL` (see §6).

---

## 2. Reusable infrastructure built (all `Qed` unless noted)

- **Capture-avoiding type substitution.** The hand-written `subst`/`hsubst`
  fixpoints in `types.v` were not capture-avoiding across the three variable
  sorts (type/row/mode); fixed (see §5), and the interp-level corollaries proved
  in `interp.v`:
  `ty_subst_single`, `row_subst_single`, `mode_subst_single`
  (`interp._ty η μ δ (τ.[τ'/]) ξ ≡ interp._ty (interp τ' :: η) μ δ τ ξ`, etc.),
  plus the renaming lemma `ty_ren`, env-shift helpers, and the OFE `Proper`
  instances the codebase was missing.
- **Pure weakest-precondition.** `prel_brel`, `prel_mono`, `prel_forall`
  (`pure_weakestpre.v`) + the pure-step determinism helpers
  (`pure_step_det_val`, `val_no_pure_step`, `nsteps_pure_step_det`).
- **Subtyping soundness** (`interp.v`, one combined-scheme induction
  `subtyping_sound_all`): `ty_le_sound` / `row_le_sound` / `sig_le_sound`
  (syntactic `le.{_type,_row,_eff_sig}` ⇒ semantic `≤ₜ`/`≤ᵣ`/`≤ₛ`). Most rules
  proved; the previously-commented `sig_le_eff` (`sem_sig.v`) and `row_le_erase`
  (`sem_row.v`) are now proved; remaining internal gaps: `TArrow_le`,
  `TRec_le`, `RUnion_le@true` (see §6).
- **The `erase_ctx` / label-structure machinery** (`interp.v`):
  `labels_l/r_interp_row` (labels of `interp._row` are η,μ-independent and equal
  a concrete list), `fresh_left/right`, `erase_ctx_row_to_disj_ctx`,
  `erase_ctx_empty`.
- **Duplicability / mode soundness** (`interp.v`): `multi_ty_sound`,
  `multi_env_sound`, `mode_env_sound`, `row_type_sub_sound`, `row_env_sub_sound`,
  `once_row_sound`, plus the shape predicates `MultiP`/`topL`/`toplike` and the
  invariant `le_ty_MultiP_topL`.
- **Effect/handler/reference compatibility lemmas** (`compatibility.v`):
  `sem_typed_effect`, the four `sem_typed_{deep,shallow}_handler_{MS,OS}`,
  `sem_typed_load_expr`, `sem_typed_store_expr`, `sem_typed_alloctape`,
  `sem_typed_randu`, `sem_typed_unpack_gen` (binder-general), and the
  recursive-closure helpers `sem_oval_typed_ufun_{mode,rec,rec_xf}`.

---

## 3. The central blocker that was resolved: the `sem_sig_later` linchpin

`sem_row_cons` (`sem_row.v`) had been changed (commit `ed6aea8a`, "changed ofe of
sem_row") to wrap the head signature in `sem_sig_later`, i.e. a `▷`. The intent
was to make `sem_row_cons` *contractive* for the recursive-row fixpoint
`sem_row_rec`. Consequences:

- `do` (effect introduction) pays that `▷` for free via later-intro; handlers
  pay it with their own reduction step.
- **`effect` and effect-*erasure* have no step to pay it**, so dropping a
  freshly-allocated `⊥`-headed signature reduced to `▷ False ⊢ False` — i.e.
  `sem_typed_effect` and `row_le_erase` were unprovable.

Investigation established this was **safe to undo**: `sem_row_cons_contractive`
is *unused* (and itself `Admitted`), recursive rows (`RRec`) are commented out of
the current syntax, and `rel`/`brel` get their contractivity from their *own* `▷`
(in `rel_pre`/`kwp_pre`), independent of `sem_row_cons`. Dropping the head
`sem_sig_later` (commit `10bb1d8b`) therefore broke nothing, and immediately made
`row_le_erase` and `sem_typed_effect` provable; the four handler lemmas + `do`
became *strictly easier* (their `sem_sig_later`-peeling steps were removed). This
unblocked the whole subtyping-soundness track.

---

## 4. The remaining 7 cases and exactly what each needs

All 7 are blocked on changes to the **core semantic judgement `bin_log_related`**
(or the operational/probabilistic model) — not on missing compatibility lemmas
(those are proved) and not on proof effort.

### 4a. `Effect`, `Do`, `DeepHandle`, `ShallowHandle` — need δ-label resolution

The fundamental goal relates the literal term `Do (EffName s) e` / `Effect s e`
(effect *name* `s`, with `s ∈ dom Δ ⊆ dom δ`). But:

- `Do (EffName _)` is **operationally stuck** (`head_step = dzero`,
  `semantics.v`); only `Do (EffLabel l)` reduces.
- the protocol theory `interp._eff_sig` at `SSig s ι κ` / `SAbs s` expects
  `do: (EffLabel (δ!!!s).1) v` on the left and `(δ!!!s).2` on the right
  (verified: `interp (SAbs s) = sem_sig_bottom (δ!!!s)` and
  `interp (SFlip m (SSig s ι κ)) = sem_sig_flip_mbang … (sem_sig_eff (δ!!!s) …)`
  hold *definitionally*).
- `bin_log_related`/`sem_typed` relate the expression **literally** (only value
  substitution `subst_map`); they never resolve `EffName s → EffLabel (δ!!!s)`.

So the related expression must be δ-resolved. This is the `lbl_resolve` redesign
(see §7), which is the correct fix.

### 4b. `App`, `Sub` — need δ-injectivity + label-ownership in `bin_log_related`

`sem_typed_app_gen` consumes `ρ' ≤ᵣ ρ` as a **persistent iProp supplied before the
brel is entered**. The sound derivation of `interp ρ' ≤ᵣ interp ρ` from the
syntactic `D ⊢ₗ ρ' ≤R ρ` goes through `row_le_sound`, whose `RErase_le` case needs
`erase_ctx D`: the label *ownership* `is_label (δ!!!s).1 DfracDiscarded` /
`spec_labels_frag (δ!!!s).2 DfracDiscarded`, and *freshness*
`(δ!!!s) ∉ labels (…)`. Those resources live **inside** the brel (in `valid` /
`distinct`), which is not yet in scope at the `≤ᵣ`-premise point. Hence
`bin_log_related` must *assume*, as hypotheses:

1. the δ-image labels are allocated/discarded (persistent), and
2. δ is injective on `dom δ` (so distinct names ⇒ distinct labels).

These are **necessary for the theorem to be true** (with aliased labels the
subtyping is unsound), not a convenience. The matching `erase_ctx` discharge
machinery (`erase_ctx_row_to_disj_ctx`, `fresh_left/right`) is already built; it
needs the goal-`ξ` `valid`/`distinct`, so either the rows are taken closed
(`abst_sigs ρ = ∅`) or `row_le_sound`/`erase_ctx` are re-stated `ξ`-monomorphic
(both are *our* lemmas, free to re-state). `sem_typed_app_gen` may also need to be
restructured so it consumes `≤ᵣ` inside the brel where the resources are
available.

`Sub` additionally needs `ctx_le_sound` (`D ⊢ₗ Γ ≤C Γ' → interp Γ ≤ₑ interp Γ'`);
its nil base case `_ctx D [] Γ' = True` currently forces the *wrong* direction
(`[] ≤ₑ Γ'`, false for non-empty `Γ'`), so the `le._ctx` definition / `Sub_typed`
rule has a polarity issue worth reviewing.

### 4c. `TRand` — needs a probabilistic-core coupling primitive

`interp TTape = sem_ty_tape` keeps two **empty, same-`N`** tapes
(`α1 ↪ (N;[])`, `α2 ↪ₛ (N;[])`) under one invariant. To inhabit the `ℕ` result,
the two reads `Rand #m #lbl:α1` / `Rand #m #lbl:α2` must yield equal values, i.e.
be *coupled*. probblaze's coupling rules only couple a labelled tape with an
*unlabelled* rand (`brel_couple_TU/UT`, `wp_couple_tape_rand/rand_tape`) or
fragment-couple by presampling (`brel_couple_TT_frag`); none couples two labelled
empty-tape reads. **Missing:** a `brel_couple_tape_tape` /
`wp_couple_tape_tape` rule (genuinely new probabilistic-core lemma). `TRandU`
(unlabelled) *is* proved.

---

## 5. Soundness bugs found and fixed in the type system

Each was confirmed (counterexample or interp mismatch) and fixed as a minimal,
authorized statement edit; see the corresponding commit.

1. **Type substitution was not capture-avoiding** (`types.v`): `hsubst_vmode_type`
   skipped the body of `TBang`; `subst_type`/`hsubst_row_type` did not shift the
   substitutend's *other-sort* (mode/row/type) variables under `TForallM`/
   `TForallR` (and `TForallT`/`TExists`/`TRec`/`SSig`), causing variable capture.
   Fixed + all `SubstLemmas`/`HSubstLemmas` re-proved. (`c3323ea2`)
2. **`MAbsElim_typed`** had `m : row` with a *row* substitution `τ.|[m/]` but
   eliminated a *mode* quantifier `∀M:τ` — incoherent. Annotated `(m : vmode)`.
   (`9a910f5c`)
3. **`TUnpack`** shifted `Γ2`/`τ2` but left the body's `ρ` and `Γ3` unshifted; also
   missing the `x ∉ ctx_dom Γ2/Γ3` freshness premises. (`9a910f5c`, `93150209`)
4. **`TAbs/RAbs/MAbs_pure`** did not shift the premise context under the new
   binder. (`93150209`)
5. **`le.TBangRef_le` is unsound** (it was author-flagged `unsure if this is
   sound`): it lets a *linear* `ref τ` be promoted to `![MS](ref τ)`, but
   `interp (TRef α) = sem_ty_ref` is a bare `↦` with no invariant, not duplicable.
   Removed. (`66d71468`)
6. **`le.OnceR`** used `RFlip MS` (vacuous, `¡[MS]=id`) where the semantic `OnceR`
   is `¡[OS]ρ ≤ᵣ ρ`. Fixed to `RFlip OS`. (`b9d53aff`)
7. **`SFlipComp_le`/`RFlipComp_le`** mode premise `_mode m' m` had the wrong
   polarity for the antitone `sig/row_le_mfbang_comp`; fixed to `_mode m m'`.
   (`b9d53aff`)
8. **`Rec_typed`/`Rec_pure_typed`** side condition `m m⪯C Γ` is too weak: the
   recursive closure's captured env must be `MultiE` (the `iLöb` self-reference
   needs it persistently), which `OS` does not give. Strengthened to `MultiC Γ`.
   (`5b115012`)
9. **`Rec_val_typed`** lacked the `f ≠ x` premise the other Rec rules carry
   (`f = x` makes the closure unsound). Added. (`b9d53aff`)
10. **`Pair_typed`/`TStore`** lacked the `ρ R⪯T τ` premise needed to carry a value
    across an effectful subexpression (matching `sem_typed_pair_gen`/
    `sem_typed_store_cpy_gen`). Added. (`fd2f5cf4`)
11. **`ShallowHandle_typed`** referenced an undefined `Γ` (compile blocker); set to
    `Γ3`, matching `App_typed`/`DeepHandle_typed`. (initial sketch commit)

> These are edits to the syntactic type system / `le` subtyping relation. They are
> all of the "fix a confirmed bug" kind, but they do change the spec — worth an
> author review.

---

## 6. Residual foundational admits (for *axiom-clean* Qed of the proved cases)

- **`le_multiT_MultiP_topL`** (`interp.v`): reduced (via `le_ty_MultiP_topL`) to the
  single sub-case where `τ` is a product/sum carrying *both* a `⊤`-component and a
  linear sibling; proving `∅ ⊢ₗ τ ≤T ![MS]τ` underivable there is a genuine
  consistency fact needing either **cut-elimination of `le._type`** or the
  (gated) `ty_le_sound`. Monotone and inversion invariants provably do not work
  (TBot/TTop/TTrans counterexamples documented in place).
- **`subtyping_sound_all`**: `TArrow_le` (needs the §4b label-ownership, i.e. the
  same `bin_log_related` change), `TRec_le` (needs a two-environment / parametric
  recursion induction), `RUnion_le@true` (routes through the still-`Admitted`
  `row_le_union`; the `@false` case is closed via `row_le_union'`).
- **Pre-existing OFE `Admitted`s** carried by the development:
  `sem_row_cons_ne`, `sem_row_cons_contractive`, `sem_ty_*_ne`, `sem_sig_*_ne`,
  etc. `sem_row_cons_ne` in particular cannot be closed as stated because the
  `sem_sig` OFE ignores the label fields — orthogonal to this work but on the
  transitive `Print Assumptions` path.

---

## 7. The `lbl_resolve` redesign — assessment: **correct route, finish it**

### 7.1 What was there before this sprint

`bin_log_related` (the semantic judgement underlying `fundamental`) related the
**verbatim** typed term. Schematically (`interp.v`, original):

```
bin_log_related ⊤ Δ Γ1 e e' ρ τ Γ2  :=
  ∀ η μ δ ξ vs, ⌜dom Δ ⊆ dom δ⌝ -∗
    sem_typed (interp Γ1) e e' (interp ρ) (interp τ) (interp Γ2)
```

and `sem_typed` in turn runs the brel on the **value-substituted** terms
`subst_map (fst<$>vs) e` / `subst_map (snd<$>vs) e'`. So the *only* substitution
performed on the term was the value environment `vs`; the effect **names** in `e`
were left exactly as written. The `δ : gmap eff_name (label*label)` parameter was
already present and was *already used by the type/row interpretation* — e.g.
`interp._eff_sig (SSig s ι κ)` builds `sem_sig_eff (δ!!!s).1 (δ!!!s).2 …` and
`interp._eff_sig (SAbs s) = sem_sig_bottom (δ!!!s)` — but it was **never applied to
the expression**. The four effect/handler typing cases (`Effect`, `Do`,
`DeepHandle`, `ShallowHandle`) were `admit`ed from the original "fundamental
sketch"; no mechanism connected them to the protocols.

(The language already had the single-name operational substitution `lbl_subst s l`
— it is what the `Effect` reduction performs and what `sem_typed_effect` is stated
in terms of — but nothing lifted it to the judgement level.)

### 7.2 Why a change is needed at all (the root cause)

This left a genuine **asymmetry**: the type/protocol side of the relation resolves
effect names to labels through `δ`, while the expression side keeps them raw. That
asymmetry is fatal for any term that performs an effect:

- **Operationally, `Do (EffName s)` is stuck.** In `semantics.v`, `head_step` of
  `Do (EffName _)` is `dzero` — only `Do (EffLabel l)` takes a step (effect names
  are *static*; at runtime the enclosing `Effect`/`let effect` allocates a fresh
  label and substitutes `EffName s ↦ EffLabel l` into its body before any `do`
  runs). So the brel's left-hand `WP (Do (EffName s) v) {{…}}` is unprovable.
- **The protocol expects a label, not a name.** `interp._row` of the effect row
  yields a theory whose entries fire on `do: (EffLabel (δ!!!s).1) v` (left) /
  `(δ!!!s).2` (right). Against a goal mentioning `Do (EffName s)`,
  `brel_introduction` simply cannot match — there is no theory entry for the
  *name*.

So `fundamental` is being asked to relate `Do (EffName s) e` (a free effect name
`s ∈ dom Δ`), but that term is neither reducible nor protocol-matching. The
information needed to make sense of it — *which label `s` denotes* — is exactly
`δ!!!s`, which the judgement already carries and already feeds to the
interpretation. The fix is to feed it to the expression too, i.e. to **close the
name/label gap on the term side**. (Confirmed in passing: with the names
resolved, the SAbs/SFlip-SSig protocol heads match the resolved term
*definitionally* — the obstacle was purely the unresolved expression.)

Note this is not optional polish: as stated, the original judgement is
*unprovable* for the effectful cases, so closing the gap is necessary for the
theorem to hold — it is not weakening to a convenient lemma.

### 7.3 What the current design does to fix it

It introduces `lbl_resolve m e` (`semantics.v`): the canonical capture-avoiding,
homomorphic generalisation of the single-name `lbl_subst` to a *map* of names, and
threads it into the judgement.

- **Definition.** `lbl_resolve m e` rewrites every **free** effect name `s` with
  `m !! s = Some l` to `EffLabel l` (`Do`/`Handle` heads consult `m`; all other
  constructors recurse homomorphically; `Val` is left untouched, as for
  `lbl_subst`). It is:
  - **capture-avoiding** for the `Effect` binder:
    `Effect s' e' ↦ Effect s' (lbl_resolve (delete s' m) e')`, so a name bound by
    an inner `effect s'` shadows the outer resolution — correct, because that `s'`
    gets its *own* fresh label at runtime, not `δ!!!s'`;
  - **identity** on the empty map / absent names (`lbl_resolve_empty` proved), and
    a strict generalisation of `lbl_subst` (`lbl_resolve_insert_subst`:
    `lbl_subst s l (lbl_resolve (delete s m) e) = lbl_resolve (<[s:=l]>m) e`).
- **Judgement change.** `bin_log_related` now relates the **δ-resolved** terms:

  ```
  sem_typed (interp Γ1)
            (lbl_resolve (resolve_l Δ δ) e)
            (lbl_resolve (resolve_r Δ δ) e')
            (interp ρ) (interp τ) (interp Γ2)
  ```

  where `resolve_l/r Δ δ : gmap string label` map each `s ∈ dom Δ` to `(δ!!!s).1`
  / `(δ!!!s).2` (`interp.v`: `resolve_map` + `resolve_map_{lookup,empty,insert,
  delete_fresh}`). The resolution domain is exactly `dom Δ`, so `lbl_resolve` is
  the **identity whenever `Δ = ∅`** — i.e. for the value/pure judgements and
  `Rec`/closure bodies (typed under `∅`), which therefore need no change.
- **How the fix closes the cases.** For `Do (EffName s)` with `s ∈ dom Δ`,
  `lbl_resolve (resolve_l Δ δ) (Do (EffName s) e) = Do (EffLabel (δ!!!s).1)
  (lbl_resolve … e)` — now reducible and protocol-matching — so the already-proved
  `sem_typed_effect` / `sem_typed_do` / handler compatibility lemmas apply.
  `Effect s e` resolves its *free* names but (by capture-avoidance) not the `s` it
  itself binds, matching the operational allocation of a fresh label.
- **Keeping the ripple mechanical.** Because `lbl_resolve` is homomorphic, every
  non-effect case is unchanged up to pushing the resolution through one
  constructor; the `lbl_resolve_*` push-through equations + a `first [ rewrite … ]`
  lead-in do this in one step, and `resolve_map` is `Opaque` so `iApply` of the
  compatibility lemmas does not force the 30-branch fixpoint during unification.

### 7.4 Assessment

This is the **right route**. It removes the precise defect (an effect-name/label
asymmetry between the expression and the interpretation), is *sound* — it relates
the program as it actually runs (names resolved to their `δ` labels, exactly as
the enclosing `Effect` would) — and the engineering keeps the change to the ~24
already-proved cases mechanical. The good pieces already exist and should be kept:
the `lbl_resolve` fixpoint + push-through equations (`semantics.v`) and
`resolve_map` + lemmas + `Opaque` (`interp.v`). What remains is the mechanical
re-proof of the ~9 regressed structural cases plus the four effect/handler cases.

**Caveat for the author.** It *does* change the statement of the headline theorem
(it now relates the δ-resolved program). I believe that is the intended reading —
the unresolved `Do (EffName s)` is a static artefact, never a runtime term — but
it is your call, which is why I have not committed it.

### 7.5 State of the current artifact

The uncommitted, *non-building* work in the tree (semantics.v / interp.v /
fundamental.v) is **leftover from an OOM-killed background process**, not a hand
edit — a partial, regressed application of exactly this fix (17 `admit`s, up from
8 at `0d8b5d5b`, because the per-case re-proof against the new goal shape is
unfinished). Don't throw the *approach* away; salvage the foundation (§7.3) and
finish the per-case re-proofs cleanly from the baseline.

---

## 8. Recommended next steps (in order)

1. **Finish `lbl_resolve`** (effects/handlers): redo it cleanly from `0d8b5d5b`
   keeping the `semantics.v`/`interp.v` foundation; re-prove the regressed
   structural cases via the push-through equations; close
   `Effect`/`Do`/`DeepHandle`/`ShallowHandle`.
2. **`App`/`Sub`**: add the δ-injectivity + label-ownership hypotheses to
   `bin_log_related`; re-state `row_le_sound`/`erase_ctx` `ξ`-monomorphically;
   discharge `erase_ctx` from the goal's `valid`/`distinct`; resolve the
   `le._ctx` nil-polarity for `Sub`.
3. **`le_multiT_MultiP_topL` / `TArrow_le` / `TRec_le`**: a cut-elimination
   (transitivity-admissibility) development for `le._type` closes the first two of
   these and unblocks `ty_le_sound` fully.
4. **`TRand`**: add the `brel_couple_tape_tape` coupling primitive.
5. **OFE `_ne` admits**: separate pre-existing cleanup (the `sem_sig` OFE may need
   to track labels for `sem_row_cons_ne`).

---

## 9. Repo state

- Clean baseline: commit **`0d8b5d5b`** on branch `prob_eff_lang` (builds; the only
  whole-tree build failure is a pre-existing broken WIP example,
  `examples/DH_KE/new_schan_ri.v`, which does not import `typing/`).
- `git stash@{0}`: an earlier, rougher crashed `lbl_resolve` attempt.
- Uncommitted working tree: the later OOM-killed `lbl_resolve` artifact
  (incomplete/regressed). The `lbl_resolve` definition + equations + `resolve_map`
  in it are worth salvaging per §7.
- 19 commits this effort (`af1132bb..0d8b5d5b`).
