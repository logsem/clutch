# Systems as factories

The uniform presentation of protocols, ideal functionalities, simulators and
their compositions, as implemented in `uc_systems.v`, with the composition
theorem built on it (`uc_theorem.v`) and the case studies of `examples/`.

## 1. Vocabulary

| notion | what it is | type |
|---|---|---|
| **session** | a value that takes its client and then its environment ports, once | `τ__F τ τ'` (ports `τ`, client `τ'`), or a two-port variant built from `τ__f` |
| **system** | a protocol, an ideal functionality, a simulator, or a composite | a **factory** `λ: <>, e` of type `fac m τ := 𝟙 -{⟨⟩}-[m]-> τ` |
| **environment** | the distinguisher; receives a system | `fac m τ → 𝔹` |

A call of a factory evaluates `e`: it allocates the session's state
(references, tapes, keys) and returns a fresh session.  The session takes
its client once (`⊸` inside `τ__F`).  The *mode* `m` of the factory says
how many sessions the environment may create: `fac OS τ = 𝟙 ⊸ τ` is
**single-session** (the thunk may be called once), `fac MS τ = 𝟙 → τ` is
**multi-session** (any number of independent instances, created and
interleaved at the environment's discretion).  See §7.

Session types, from `comp_operators.v`:

```
τ__F τ τ'    := ∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{¡θ₁ ∪ θ}-∘ 𝟙) ⊸ (∀ᵣ θ₂, τ θ₂ -{¡θ₂ ∪ θ}-∘ 𝟙)
τ__f θ τ1 τ2 := ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τ2 θ2) -{¡θ1 ∪ ¡θ2 ∪ θ}-∘ 𝟙       (a two-port client/ports bundle)
```

## 2. Why factories

Making every system a *value* is what makes the composition infrastructure
uniform.

1. **No closedness premises.**  Substitution never enters a value
   (`subst_map vs (Val v) = Val v`), so no `is_closed_expr` hypotheses
   appear anywhere: not in the operator lemmas, not in the composition
   theorem, not in the case studies.
2. **No value-position constraints.**  The composition theorem reasons about
   hybrid contexts such as `λ x. (x ||ᵣ A₀) ∘f ρ`.  With `A₀` and `ρ` values,
   the hole is always the next redex under right-to-left evaluation, and a
   reduction step is a β-step on a value.  A composition theorem over
   expressions has to ask for some components to be values and forces
   artificial value versions of the protocols.
3. **One shape for everything.**  A composite of factories is a factory, so
   protocols, functionalities, simulators and composed systems all have the
   same type constructor `fac`, and the same operators apply at every level.
4. **Games already are factories.**  `DH_real`, `DH_rand`, `enc_real`,
   `prf_real` … are thunks; reductions such as `C_lazy` force them.  The
   factory view extends this to the systems.

## 3. The factory operators (`uc_systems.v`)

```
fac_op o F G  := λ: <>, o (F #()) (G #())          a value, for values F and G
F ∘f G  := fac_op func_comp F G
F ||ᵣ G := fac_op parallel_composition F G
F ∘F G  := fac_op functionality_composition F G

fac_app o     := λ: "F" "G", λ: <>, o ("F" #()) ("G" #())   the same as a program
e1 ∘fₚ e2, e1 ||ᵣₚ e2, e1 ∘Fₚ e2                           (only for contexts with a hole)
```

A composite of systems is a system: `fac_op o F G` is the factory (a
value, a literal thunk) whose session calls the two factories, right to
left like any application, and composes the two sessions with the session
operator `o`.  The program-level `fac_app o` is the same operator as a
program; it is used only where a hole has to be filled, in the hybrid
contexts of the composition theorem and in reduction environments, and it
evaluates to `fac_op` in four pure steps (`fac_app_pure`).  Typing,
congruence and associativity are proved once for `fac_op` and instantiated
for the three operators.

The three symbols are the ones of the paper and are reserved for the
factory operators; they live in `factory_scope`, delimited `%fac`, which a
file that works with systems opens.  The session-level operators of
`comp_operators.v` are written `∘fₛ`, `||ᵣₛ`, `∘Fₛ`; they occur only in the
operator library itself and in the few core lemmas that compose a pending
session call.

Why two "functionality" operators: `F ∘f G` wraps a one-port `G`
entirely (`F` provides all of `G`'s ports), while `F ∘F G` attaches `F` to
the second port of a two-port `G` and lets the first port through to the
environment.  The latter is what a simulator for π needs inside the
`(F ||ᵣ A₀)`-hybrid world.  A single n-port operator with a port index would
subsume both; this is an open point (§8).

### Typing and congruence

`fac_op_typed`: for a session operator `o : τF ⊸ τG ⊸ τ` and related
systems `F ≈ F' : fac m τF`, `G ≈ G' : fac m τG`,
`fac_op o F G ≈ fac_op o F' G' : fac m τ`, at any mode `m` (the composite
captures nothing but the two factories).  This is typing and congruence in
one.  The instances:

| lemma | composite type |
|---|---|
| `func_comp_f_typed_gen` | `fac m (∀ᵣ θ, M θ ⊸ T4 θ)`, `fac m (∀ᵣ θ, T1 θ ⊸ M θ)` give `fac m (∀ᵣ θ, T1 θ ⊸ T4 θ)`, for η-expandable `M` |
| `func_comp_f_typed` | `fac m (τ__F τ1 τ2)`, `fac m (τ__F τ2 τ3)` give `fac m (τ__F τ1 τ3)` |
| `parallel_comp_f_typed` | `fac m (τ__F τ2 τ2')`, `fac m (τ__F τ1 τ1')` give `fac m (∀ᵣ θ, τ__f θ τ1' τ2' ⊸ τ__f θ τ1 τ2)` |
| `functionality_comp_f_typed` | `fac m (τ__F τ2 τF)`, `fac m (∀ᵣ θ, τ1' θ ⊸ τ__f θ τ1 τF)` give `fac m (∀ᵣ θ, τ1' θ ⊸ τ__f θ τ1 τ2)` |

The program-level operators are typed as values by `fac_app_val_typed`
(`fac m τF ⊸ fac m τG ⊸ fac m τ`; the arrows are `⊸` because a partial
application captures a one-shot factory) with the instances
`func_comp_app_typed(_gen)`, `parallel_comp_app_typed`,
`functionality_comp_app_typed`; they are used for the open terms of the
hybrid contexts.  The session-level value typings (`func_comp_val_typed`,
`parallel_comp_val_typed`, `functionality_comp_val_typed`, with `eta_ty`)
live in `uc_systems.v` as well.

### Associativity

Eight lemmas, each for related systems `F F'`, `G G'`, `J J'` at factory
types, at any mode:

```
func_comp_f_assoc(_rev)                       F ∘f (G ∘f J)   ≃  (F ∘f G) ∘f J
func_comp_parallel_comp_f_assoc(_rev)         (F ∘f G) ||ᵣ J  ≃  F ∘F (G ||ᵣ J)
functionality_comp_func_comp_f_assoc(_rev)    (F ∘F G) ∘f J   ≃  F ∘F (G ∘f J)      (one-port J)
functionality_comp_func_comp_f_assoc_gen(_rev)  same, two-port J
```

All eight are one-line instances of two generic lemmas.  A session-level
law is packaged as `sess_law o1 o2 o1' o2' τF τG τJ τ` (the relation
`o1 (o2 f g) j ≃ o1' f (o2' g j)` between session terms for related `f`,
`g`, `j`, exactly the `_core` form of §4) or its mirror image
`sess_law_R`; `fac_assoc_L` and `fac_assoc_R` prove that such a law holds
for the composites.  Their proof is operational: call the composite, create
J's session (it is created before the inner composite's session on both
sides), reduce the inner composite's call, and hand the remaining session
terms to the law.  Adding a new law costs its session-level proof and one
line.

## 4. The session level (`comp_operators.v`)

The operator library defines the three session operators, the session
types `τ__F` and `τ__f`, and the seven associativity cores
`func_comp_assoc(_rev)_core`, `func_comp_parallel_comp_assoc(_rev)_core`,
`functionality_comp_func_comp_assoc(_gen)(_rev)_core`: `brel` statements
for pairs of *expressions*, linear, with postcondition `τ ∗ [] ⊨ₑ vs`.
The expression form is the primitive because the factory lemmas apply a
core to the terms `F #()`, `G #()` and a session value, not to closed
self-related expressions.

## 5. Proof idioms

* `fac_closure`: `sem_typed [] e1 e2 ⊥ τ [] ⊢ ⊨ᵥ (λ: <>, e1) ≤ (λ: <>, e2) : fac m τ`.
  A relation between session bodies lifts to their factories, at any mode;
  the typing `X_typed m` of a system is `fac_closure` followed by the
  typing of its body.
* `sem_typed_fac_call`: calling a factory, with environment threading.
* The pure-step tactics find β-redexes syntactically (`RecV` applied to a
  value), on purpose, so that definitions are not unfolded.  A definition
  that should step nevertheless declares `AsRecV X f x _ := eq_refl`
  (`proofmode.do_pure_step_app_as_recv`); `fac_op o` and every factory of
  the case studies do, so no `unfold` is needed to call a factory or an
  operator.
* Evaluation is right to left: in `F ∘f G` the factory `G` is called first.
* **Top-level relations are proved directly on factories.**  Pattern, from
  `dhke/advantage_dhke.v`: intro the judgement (both sides are values:
  `iApply brel_value`), prove the relation at mode `MS` (`iModIntro`; any
  mode follows by `fac_MS_le`), call the composite, then exactly as many
  pure steps as reach the first leaf body (`brel_pures_l n%nat`), and bind
  the leaves with the per-component core lemmas.  A leaf that is still in
  function position when an inner composite is bound is a pending thunk
  call; the core lemma for that composite takes it as an argument `D1`
  with `rtc pure_step D1 (X #())` (`DH_SIM_F_KE_C_DH_rand`), and the
  consumer passes the call itself (`rtc_refl`).  Systems whose relation is
  proved in one piece (the channels, secure addition) allocate all state at
  the head, in evaluation order, and then relate one client call.
* `advantage_pure_l/_r` (`uc_advantage.v`): the advantage is invariant
  under pure steps of a system in a handler-free context, e.g. between the
  application `C_lazy d` and its value `λ: <>, C_lazy_sess d`.
* **Instance arguments.**  In a section with two instances of the same
  class (`fin_val` for messages and ciphertexts, `fin_val_type_struct` for
  their structs), a definition whose instance is not fixed by its other
  arguments gets the one declared last by typeclass resolution, silently,
  and a later unification against the intended type diverges instead of
  failing.  Such definitions take the instance explicitly
  (`Arguments … ms`, `… msg cipher` after the section) and callers pass it.
* **Folded type names.**  `iApply` of an operator-typing lemma against a
  goal whose type is a folded name loops in unification; `rewrite /τ_X`
  first, or pass the three type functions explicitly.

## 6. The composition theorem (`uc_theorem.v`)

With a side functionality `A₀` (all seven systems are values; `Rπ` is the
real system `H ∘f π`, of which only the port type `τH` and the advantage
bound are visible):

```
S  : fac m (τ__F τH τF)         F  : fac m (τ__F τF τJ2)        A₀ : fac m (τ__F τA τJ1)
ρ  : fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τJ1 τJ2)
S' : fac m (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{¡θJ ∪ θ}-∘ 𝟙) ⊸ τ__f θ τA τF)
G  : fac m (∀ᵣ θ, τc θ ⊸ ∀ᵣ θJ, τG θJ -{¡θJ ∪ θ}-∘ 𝟙)

(∀ A : fac m (τ__F τH τJ2) → 𝔹,                   advantage A Rπ (S ∘f F) #b ≤ ε_π A) →
(∀ A : fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τF) → 𝔹,   advantage A ((F ||ᵣ A₀) ∘f ρ) (S' ∘f G) #b ≤ ε_ρ A) →
∀ A : fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τH) → 𝔹,
  advantage A ((Rπ ||ᵣ A₀) ∘f ρ) ((S ∘F S') ∘f G) #b
    ≤ ε_π (λ t, A ((t ||ᵣₚ A₀) ∘fₚ ρ)) + ε_ρ (λ t, A (S ∘Fₚ t))
```

and the variant `uc_composition_f` without `A₀`, using `∘f` only.  All
components are values, there are no closedness or substitution premises,
and the systems in the conclusion and in the hypotheses are composites
(values).  The reduction environments in the bound use the program-level
operators, since they have a hole.  The chain of hybrids: the perfect
steps are the factory associativity lemmas; each reduction step first
exchanges a composite for the program-level context applied to the system
(`hybrid_pure`, `sim_pure`, through `advantage_pure_*`) and then applies
`advantage_reduction_ctx` (in `uc_advantage.v`, together with
`advantage_zero` and `ctx_adv_typed`); the substitution side condition is
`simpl; rewrite` because the context is made of values.  Only the standard
classical axioms are used.

Instances: `dhke_chan_realises` (DHKE under the mask channel),
`dhke_ske_realises` (DHKE under the SKE channel, then `adv_composition_prf`
with the PRF-based scheme), `auth_dhke` (DHKE over the authenticated-channel
protocol, with `uc_composition_f`).

## 7. Single versus multi-session

**The two notions in UC.**  Canetti's emulation is *single-session*: the
environment interacts with one instance of the challenge protocol (the test
session); it may simulate other protocols internally, but there is only one
real instance.  *Multi-session* emulation, where the environment itself
creates and interleaves many instances of the challenge protocol, is a
derived notion: it is the composition theorem applied to the protocol "run
n copies of π", proved by a hybrid argument over instances with a loss
linear in n.  UC therefore takes single-session as the hypothesis and gets
multi-session as a consequence.

**The two modes here.**  The mode of the factory type is exactly this
distinction:

| mode | factory type | environment may | hypotheses of `uc_composition m` |
|---|---|---|---|
| `OS` | `fac OS τ = 𝟙 ⊸ τ` | create one instance | single-session realisations, the classical statement |
| `MS` | `fac MS τ = 𝟙 → τ` | create any number of independent instances | multi-session realisations |

In both modes a *session* is one instance, used once (`τ__F`): an `MS`
factory makes fresh state per call, it does not share state between calls.
(`secure_add3` is the one example where an instance serves several
clients: there the environment runs any number of sessions on one
instance, which is the inner `→` of `τ_ADD3`, and the factory on top of it
is of either mode like everywhere else.)

**Everything is mode-generic.**  `fac_op`, its typing, the congruences, the
associativity lemmas and `uc_composition` take the mode as a parameter; the
only mode-sensitive steps are closure introductions (a multi-shot thunk may
capture only multi-shot factories, which `fac MS` are) and the `□`
introduction in the associativity proofs, which goes through because all
hypotheses there are factory relations, hence persistent.

**Why the examples are multi-session for free.**  A relation between
session bodies `sem_typed [] e e' ⊥ τ []` is persistent, so `fac_closure`
lifts it to `λ<>, e ≈ λ<>, e'` at `fac MS τ` just as at `fac OS τ`: every
perfect step of every case study, proved once per instance, is a
multi-session step.  Only the computational steps change meaning.  In DHKE
the reduction `λ d, A (F_AUTH ∘f C_lazy d)` calls the DDH oracle `d` once
per instance, so at mode `MS` the DDH term of the bound is the advantage
of a multi-query distinguisher against the thunks `DH_real`/`DH_rand`,
i.e. multi-instance DDH (equivalent to DDH by random self-reducibility,
but a different assumption formally).  Hence one parametrised statement

```
adv_DHKE m :  ∀ A : fac m τ_DH → 𝔹,
  advantage A (F_AUTH ∘f DH_KE) ((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice) #true
    ≤ advantage (λ d, A (F_AUTH ∘f C_lazy d)) DH_real DH_rand #true
```

covers the classical result (`m = OS`, single-instance DDH) and the
multi-session result (`m = MS`, multi-instance DDH); the channels and the
composed systems follow the same pattern.  Where a computational
assumption is only available for one-shot oracles (the PRF-based scheme,
`adv_enc_prf`), the front-end theorem is stated at `OS`.

**What is not available.**  Deriving `MS` from `OS` by the UC hybrid over
instances needs a bound on the number of instances, which `𝟙 → τ` does
not carry.  It would be a separate theorem over a bounded-call factory
type (§8); the framework does not depend on it.  In this development
multi-session security is obtained directly, from the same per-instance
relational proofs, with multi-instance computational assumptions.

## 8. Open points

* **n-port systems.**  `∘f`/`∘F` and `τ__F`/`τ__f` are the one- and two-port
  cases written by hand.  A port-indexed operator (or a regrouping adapter)
  would make `∘F` an instance of `∘f`.
* **η-expandability premise** of `func_comp_f_typed_gen`
  (`eta_ty (M θ)`): inherited from the session-level `func_comp`, which
  η-expands the client.  Discharged for all arrow-shaped interfaces.
* **Bounded modes.**  An `n`-shot mode `![n] τ` is cheap semantically (the
  `n`-fold separating conjunction of `τ` on the pair of values, so that
  `![MS] τ ≤ ![n] τ ≤ ![OS] τ` and a factory of mode `n` is `n`
  single-session factories, which is what a hybrid over instances
  consumes); its compatibility rules are a closure rule for persistent
  captures and an application rule that uses up one copy, and `n`-shot
  continuations are `MS` continuations at a bounded-use type.  The
  syntactic type system would need an `n`-indexed bang for the same rules,
  which is the larger part.
* **The two channel variants.**  The theories of the mask channel
  (`sec_channel_prf.v`) and of the SKE channel (`ske_sec_chan_common.v`)
  are parallel but not identical (persistent versus linear continuations,
  group elements versus an abstract message space), and both relation
  proofs depend on that shape; a shared parametrised theory is a rewrite
  of those proofs.
* **Oblivious transfer** (`examples/ot/`) is not yet on factories.

## 9. File layout

The framework is `probblaze/uc/`: `comp_operators.v` (the three session
operators, the session types and the seven associativity cores),
`advantage.v`, `uc_systems.v`, `uc_advantage.v`, `uc_theorem.v`.  Each
case study lives in one folder of `examples/` (`dhke`, `auth`,
`secure_channel` with both channel variants and their compositions with
DHKE, `secure_add`, `secure_add3`, `prf`, `ot`), with files `<comp>_def.v`
(programs and the systems `REAL_*`, `IDEAL_*`, `SIM_*`, `RED_*`),
`<comp>_typing.v`, `<comp>_prf.v` or per-component core files (the
relations), and `advantage_<comp>.v` (the top-level statement).  Systems
are factories with their bodies inline; the only named session bodies are
the oracle-parametrised reductions `C_lazy_sess` and `RED_CHAN_sess`, and
the per-instance sessions of `secure_add3`.
