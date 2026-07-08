# `functionality_comp_func_comp_assoc` is mis-fit for `DHSIM_FKE_CHAN3 ↔ CHAN4`: BOTH its G- and J-premises are uninhabitable for the terms supplied

**Status:** the two top-level lemmas `DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4` and
`DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3` (`new_composition.v:158,169`) apply
`functionality_comp_func_comp_assoc(_rev)` and discharge its premises with
`F_KE_F_OAUTH_typed` (the **G**-slot) and `CHAN_body_typed` (the **J**-slot). **Both of
those premises are uninhabitable as stated** — the combinator's premise shapes assume
fewer client interfaces than the actual terms (`F_KE_lazy_alice ||ᵣ F_OAUTH`, `CHAN`)
have. So those two equivalences currently rest on two unprovable admits. Left
`Admitted` pending a design decision. **All 8 other building-block lemmas are proved
(`Qed`)**; these two are the only blockers, and they share one root cause.

The two failures are documented in turn below (§1 G-slot, §2 J-slot), then the shared
root cause and fix options (§3).

---

## §1 — G-slot: `F_KE_F_OAUTH_typed` is uninhabitable (client-arity mismatch)

## TL;DR

`F_KE_F_OAUTH_typed` was hoisted with the type demanded by
`functionality_comp_func_comp_assoc`'s **G-premise**, in which the client interface
is a **single** `chan`-handler returning `𝟙`. But the term it must type,
`F_KE_lazy_alice ||ᵣ F_OAUTH = right_composition F_KE_lazy_alice F_OAUTH`, applies its
client to **two** curried interfaces (`f h₂ h₁`). No value inhabits the stated type
for this term: driving any proof forces the subgoal `brel (#() h₁) (#() h₁) {{𝟙}}`,
a **stuck application of unit**, which no BREL rule can advance.

The mismatch is not local to `F_KE_F_OAUTH_typed` — it is inherited from the
combinator, so `DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4` (and `_rev`) currently rest on an
unprovable premise. This was masked while the premise was `Admitted`.

## The current (uninhabitable) statement

`new_composition_typing.v`:

```coq
Lemma F_KE_F_OAUTH_typed :
  ⊢ sem_typed [] (F_KE_lazy_alice ||ᵣ F_OAUTH) (F_KE_lazy_alice ||ᵣ F_OAUTH) ⊥
      ((∀ᵣ θ, hdl chan θ ⊸
         (∀ᵣ θ1, oaleak θ1 ⊸ ∀ᵣ θ2, leakI θ2
                 -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T) [].
```

Here `hdl chan θ = ∀ᵣ θ', chan θ' -{θ'⊎θ}-∘ 𝟙` — a **single**-interface client.

This type was derived by inspecting the residual goal after
`iApply functionality_comp_func_comp_assoc` in `DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4`; it is
exactly that combinator's `G`-premise instantiated with `τJ=chan`, `τ1=oaleak`,
`τF=leakI`.

## Why it is uninhabitable

`||ᵣ` is `right_composition` (in `p_composition.v`). Unfolded:

```coq
right_composition F₁ F₂
  = λ "f" "r₂" "r₁", F₁ (λ "h₁", F₂ (λ "h₂", "f" "h₂" "h₁") "r₂") "r₁"
```

So for `F₁ = F_KE_lazy_alice`, `F₂ = F_OAUTH`, the client `"f"` is applied to **two**
curried interface arguments: `"f" "h₂" "h₁"` where

- `"h₂"` = the **chan** interface handed in from `F_OAUTH`'s client slot, and
- `"h₁"` = the **gk** interface handed in from `F_KE_lazy_alice`'s client slot.

Operationally `f : chan-iface → gk-iface → 𝟙`, i.e. it consumes **two** interfaces.

But the stated type gives `f : hdl chan θ`, i.e. `f (chan-iface) →* #()`. Then
`f h₂ h₁ = (f h₂) h₁ →* #() h₁` — applying the unit value `#()` to `h₁`, which is
**stuck** (`#()` is not a lambda). Concretely, when the self-refinement binds on
`f1 u1` (whose result is `#()` by the client hypothesis `Hf : hdl chan θ f1 f2`), the
continuation is `brel (v1 w1) (v2 w2) {{𝟙}}` with `v1 = v2 = #()`. That subgoal is
unprovable:

- `brel_value` fails — `#() h₁` is not a value;
- `brel_pures'` is a no-op — a stuck application cannot step;
- `fupd_brel` only adds a modality; `brel_wand` defers circularly.

No strategy (composition *or* self-refinement) escapes this, because it is forced by
the term/type disagreement, not by proof tactics.

## Positive control (the term's real type)

`right_composition F_KE_lazy_alice F_OAUTH` **is** typeable — at the two-interface
type, via `parallel_comp_right` from the proven atomics
`F_KE_lazy_alice_typed : τ__F leakI gk` and `F_OAUTH_typed : τ__F oaleak chan`:

```coq
iApply (parallel_comp_right F_KE_lazy_alice F_KE_lazy_alice F_OAUTH
          θ oaleak leakI chan gk);
  [ iApply F_KE_lazy_alice_typed | iApply F_OAUTH_typed ].
```

yielding (for a Coq-level `θ`, **no** outer `∀ᵣ θ`):

```coq
sem_typed [] (F_KE_lazy_alice ||ᵣ F_OAUTH) (F_KE_lazy_alice ||ᵣ F_OAUTH) ⊥
  ((τ__f θ chan gk) ⊸
     (∀ᵣ θ1, ∀ᵣ θ2, oaleak θ1 ⊸ leakI θ2
             -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙)) []
```

Differences from the current (broken) statement:

| aspect          | broken statement                          | real type (via `parallel_comp_right`)        |
|-----------------|-------------------------------------------|----------------------------------------------|
| client input    | `hdl chan θ` (single chan interface)      | `τ__f θ chan gk` (chan **and** gk)           |
| output quantifiers | `oaleak θ1 ⊸ ∀ᵣ θ2, leakI θ2 -∘ 𝟙`     | `∀ᵣ θ1, ∀ᵣ θ2, oaleak θ1 ⊸ leakI θ2 -∘ 𝟙`   |
| `θ` binding     | outer `∀ᵣ θ`                              | Coq-level parameter (no outer `∀ᵣ θ`)        |

The two-interface client is what `right_composition` actually needs: `f h₂ h₁` = feed
`chan` (θ1) then `gk` (θ2).

## §2 — J-slot: `CHAN_body_typed` is uninhabitable (the J-body is a lambda, not a `𝟙`)

The **same** combinator's **J**-premise fails for the **same** structural reason — this
time the J-body has *more* interfaces than the premise's type allows.

`functionality_comp_func_comp_assoc`'s J-premise (`p_composition.v:432`) types `J` at
`𝟙` under a **2-variable** environment `[("f", …); ("x", …)]`, and its proof
(lines 478–489) closes `BREL (subst_map … J) {{𝟙}}` from that premise applied to the
un-applied J-value. That only fits a `J` whose body is a **`𝟙`-computation** (runs and
returns `#()`).

But `CHAN = λ: "f" "ChanOp" "doGK", <inner>` (`sec_channel_def.v:57–58`) is a
**3-argument** function. After `functionality_comp_func_comp_assoc` abstracts `f` and
`ChanOp` (via `λ: f x, J`), the residual J-body is `CHAN_body = λ: "doGK", <inner>` — a
**lambda value** (CHAN is a getKey *consumer*: it takes the `doGK` handle as a third
external argument). `CHAN_body_typed` types it at

```coq
sem_typed [("f", hdl cli θ); ("ChanOp", chan θJ)] CHAN_body CHAN_body (θJ∪θ) 𝟙 []
```

i.e. the lambda `λ doGK, inner` at `𝟙 = sem_ty_unit`, which demands the value equal
`#()`. Empirically (scratch): the goal reduces to
`brel ⊤ (λ: "doGK", …)%V (λ: "doGK", …)%V _ {{𝟙}}`; `iApply brel_value; iIntros "$ !>"`
leaves `𝟙 (λ doGK, …) (λ doGK, …) = ⌜(λ doGK, …) = #()⌝`, which is **false**;
`brel_pures'` is a no-op (already a value). So the premise is unprovable.

**Contrast with `F_KE_body` (proved):** its body begins `let (…) := "effs" in …` — a
computation that builds its own `doGK` *internally* and returns `𝟙`. F_KE is a getKey
*provider*; CHAN is a getKey *consumer*, so CHAN's body cannot be a `𝟙`-computation.

## §3 — Shared root cause

`functionality_comp_func_comp_assoc` (`p_composition.v`, ~line 430) is written for a
`G` that is a **functionality** (single-interface client) and a `J` whose body is a
**`𝟙`-computation** under a 2-var env:

```coq
(* G-premise *)  sem_typed [] G G ⊥
  (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{θJ⊎θ}-∘ 𝟙) ⊸ ∀ᵣ θ1, τ1 θ1 ⊸ ∀ᵣ θ2, τF θ2 -{…}-∘ 𝟙) []
(* J-premise *)  sem_typed [("f", …); ("x", …)] J J … 𝟙 []
```

But `DHSIM_FKE_CHAN3` / `DHSIM_FKE_CHAN4` instantiate it with
`(F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f (CHAN …)`, where:

- `G = F_KE_lazy_alice ||ᵣ F_OAUTH` is a **parallel** composition — a *two*-interface
  client (chan for F_OAUTH + gk for F_KE), not a single-interface functionality; and
- `J = CHAN …` is a getKey **consumer** — a *three*-argument function whose residual
  body is a lambda over `doGK`, not a `𝟙`-computation.

In both cases the combinator's **conclusion** still unifies syntactically with the term
(so the file builds while the premises are admitted), but the **premises** describe
terms with fewer interfaces than reality and can never be discharged. This is one
design mismatch surfacing in two slots — the combinator was written for a simpler
composite shape than CHAN3/CHAN4 actually are.

## Affected proofs

- `new_composition.v:158` `DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4`
- `new_composition.v:169` `DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3`

Both `iApply functionality_comp_func_comp_assoc(_rev)`, then discharge the G-premise
with `iApply F_KE_F_OAUTH_typed` (§1) and the J-premise with `iApply CHAN_body_typed`
(§2). They are `Qed` **only** modulo these two unprovable admits. (The neighbouring
`DHSIM_FKE_CHAN2 ↔ DHSIM_FKE_CHAN3` re-association uses a *different* combinator,
`func_comp_parallel_comp_assoc`, which is fine — its premises are
`F_AUTH_DH_SIM_typed_val` + `F_KE_body_typed` + `F_OAUTH_typed`, all proved.)

## Candidate fixes (your call)

1. **Fix the combinator + restate both premises.** Change
   `functionality_comp_func_comp_assoc(_rev)` so that (a) its **G-premise** takes the
   two-interface (`τ__f θ chan gk`) client shape — then `F_KE_F_OAUTH_typed`, restated to
   the §1 real type, is provable by `parallel_comp_right`; and (b) its **J-premise**
   types `J` as a getKey-**consumer** (`∀ᵣ θ', gk θ' -{θ'⊎θJ⊎θ}-∘ 𝟙`) rather than at
   `𝟙` — then `CHAN_body_typed`, restated to that type, is provable by reusing
   `CHAN_typed`'s body. Re-derive the combinator's conclusion accordingly and re-check
   `DHSIM_FKE_CHAN3 ↔ 4`. Touches shared `p_composition.v` and `new_composition.v`.
   **Risk:** the combinator relates `(F ∘F G) ∘f J` to `F ∘F (G ∘f J)`; changing `G`'s
   and `J`'s interface arities ripples into the `∘F`/`∘f` composed terms, the modality
   rows, and the `F` premise — this is a genuine re-derivation of the lemma, not a
   surface edit.

2. **Restructure `DHSIM_FKE_CHAN3`.** If `G` is genuinely meant to be a single-`chan`
   functionality, the term should not be `right_composition` (which passes the gk
   interface `h₁` into the client). Re-derive the CHAN3 term so the client consumes only
   `chan`, or choose a re-association combinator whose G-slot accepts a two-interface
   parallel composition.

3. **Sanity-check the combinator itself.** Confirm `functionality_comp_func_comp_assoc`
   is even the intended combinator for a CHAN3→CHAN4 re-association where the middle
   stage is a `||ᵣ`; the single-interface G-premise suggests it was written for a
   functionality `G`, not a parallel composition.

## How to reproduce / verify

G-slot (§1):
- Unfold `right_composition` (`p_composition.v`) and read the client application `f h₂ h₁`.
- Read `functionality_comp_func_comp_assoc`'s G-premise (`p_composition.v` ~430).
- In `new_composition_typing.v`, attempt `F_KE_F_OAUTH_typed`: after intro'ing the
  single-interface client and `brel_pures'`, the goal stalls at `brel (#() _) (#() _) {{𝟙}}`.
- Contrast: `parallel_comp_right` (shown above) closes the *two-interface* statement.

J-slot (§2):
- Read `CHAN = λ: "f" "ChanOp" "doGK", …` (`sec_channel_def.v:57–58`) — 3 arguments.
- Read `functionality_comp_func_comp_assoc`'s J-premise + its use (`p_composition.v:432`,
  478–489): `J` typed at `𝟙` under `[f; x]`.
- In `new_composition_typing.v`, attempt `CHAN_body_typed`: `iApply brel_value; iIntros "$ !>"`
  leaves `𝟙 (λ doGK, …) (λ doGK, …)` = `⌜(λ doGK, …) = #()⌝`, which is false.
- Contrast: `CHAN_typed` (proved) types the *whole* `CHAN` — including the `doGK`
  argument — at `∀θ, hdl cli θ ⊸ τ__f θ chan gk`, i.e. treating getKey as an interface,
  which is the shape the J-premise would need.
