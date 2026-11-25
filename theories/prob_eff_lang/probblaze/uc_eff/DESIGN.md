# Modules: a redesign of the UC layer

Status: a design proposal with a first mechanisation. The existing
development in `uc/` and `examples/` is untouched. Section 7 says what is
proved; code outside sections 4 and 5 is pseudocode traced by hand.

## 1. Why change anything

In `uc/`, every protocol, functionality and simulator allocates a private
effect label, hands its client closures that perform it, and handles it.
Every such handler in the case studies is tail-resumptive: it computes a
result and resumes the continuation exactly once, last. A deep
tail-resumptive handler for a label that only escapes through a closure is a
function call:

    effect l in handle f (λ x. do l x) with l x, k ⇒ k (h x)    ≃    f h

So these handlers do no control-flow work. They cost private label rows per
component, two session types, three composition operators, eight
associativity laws, two composition theorems, and a fresh-label and
exhaustion step in every proof.

## 2. Where effects are necessary

Without control operators, an environment that interacts with a component
through calls and callbacks can only produce well-bracketed (last-in,
first-out) schedules: a callback may start new port calls, but they must
finish before the callback returns.

* DHKE needs only nested schedules.
* Two concurrent rounds do not: if A runs `send a1; recv b1; send a2; recv b2`
  and B the mirror image, A blocks at `recv b1`, B (nested) blocks at
  `recv a2`, and A cannot be resumed. Three-party addition has this shape
  (`examples/secure_add3/scheduler_typed.v`).
* With one-shot ports, a secure channel over a key exchange also needs it:
  Bob must wait at his delivery while Alice finishes her key exchange and
  sends.

Claim: effects are needed for non-well-bracketed scheduling of direct-style
parties, and the only role that must capture a continuation is the
adversary. The components need none.

## 3. The design

**Module.** A module is a closed value that takes the operations it uses
and returns the operations it offers. Applying it creates an instance: it
allocates the instance's state. Its type is

    Mod X Y ≜ ∀θ. X θ → Y θ

for interfaces `X`, `Y` (types indexed by the row `θ` of the environment's
effects). A module contains no handler and allocates no label.

    functionality   F : Mod Adv_F Ports      takes its adversarial operations
    protocol        ρ : Mod Ports_F Ports    takes the ports below it
    simulator       S : Mod Adv_R Adv_F      implements the ideal adversarial
                                             operations with the real ones

**One composition operator.** `g ⊳ f ≜ λ a. g (f a)`. A protocol on a
functionality is `ρ ⊳ F`; a simulator attached to a functionality is
`F ⊳ S`; two simulators compose to `S' ⊳ S`. Moving a simulator past a
protocol is associativity.

**Honest ports are one-shot.** A port that an honest party calls once is
an affine function. This removes the "first call only" guards and
option-reference bookkeeping of the existing code. Ports that are
multi-use or handed to the adversary are unrestricted and keep guards.

**One-shot rows.** Ports run at the row `¡θ`: the environment resumes a
suspended party at most once. The DHKE proof needs this (to carry tape
ownership across a call to the adversary), and the statements are
presumably false for a rewinding adversary.

**Environment.** `A : Mod X P → 𝔹` creates an instance by applying the
module to operations that perform its own effects, calls the ports, and
handles those effects. Its handler may capture a blocked party and run
another. This is the only place a handler occurs.

**Realisation.** `R` realises `F` with simulator `S` up to `ε` when
`advantage A R (F ⊳ S) ≤ ε A` for every typed `A`.

**Composition theorem** (`modules.v`).

    advantage A Rw (F ⊳ S) ≤ ε A                    for all typed A
    advantage A (ρ ⊳ F) (G ⊳ S') ≤ ε' A             for all typed A
    ⊢ advantage A (ρ ⊳ Rw) (G ⊳ (S' ⊳ S))
        ≤ ε (λ v. A (ρ ⊳ v)) + ε' (λ v. A (v ⊳ S))

Proof: `ρ ⊳ Rw ≤ ρ ⊳ (F ⊳ S) ≃ (ρ ⊳ F) ⊳ S ≤ (G ⊳ S') ⊳ S ≃ G ⊳ (S' ⊳ S)`.
Nothing is assumed about `Rw`. The composed simulator is a single
simulator, so realisation is closed under composition. The two
environments on the right are `A` extended by the protocol above the
module it is given, and by the simulator below it.

**Side functionalities** are placed next to a module with a tensor
(`modules.v`),

    f ⊗ g ≜ λ a. let u = f (fst a) in let v = g (snd a) in (u, v)
    f : Mod X Y,  g : Mod X' Y'  ⊢  f ⊗ g : Mod (X × X') (Y × Y')

and a simulator leaves the other component alone as `S ⊗ id`. The law that
moves a simulator out of a tensor is interchange,

    (g ⊳ f) ⊗ h  ≃  (g ⊗ h) ⊳ (f ⊗ id)

and `λ v. A (v ⊗ h)` is `A` extended by a module `h` beside the one it is
given. A module body runs without effects, so the interfaces it holds,
which may be affine, are kept across the calls it makes; that is what
makes the tensor well typed.

## 4. DHKE (mechanised: `dhke.v`, `dhke_proof.v`, `dhke_typing.v`)

The initiator is `#true`, the responder `#false`.

    F_AUTH (leak, deliver) ≜
      let mA = ref None in let mB = ref None in
      -- the initiator's endpoint
      ( ( λ m.  mA := Some m; leak (true, m)
        , λ (). if deliver true then !mB else None )
      -- the responder's endpoint
      , ( λ m.  mB := Some m; leak (false, m)
        , λ (). if deliver false then !mA else None ) )

    DH_KE ((sendA, recvA), (sendB, recvB)) ≜
      let α, β = new tapes in
      -- the initiator
      ( λ (). let a = rand(α) in sendA (g^a);
              match recvA () with None ⇒ None | Some B ⇒ Some (B^a)
      -- the responder
      , λ (). match recvB () with None ⇒ None
              | Some A ⇒ let b = rand(β) in sendB (g^b); Some (A^b) )

    F_KE (notify, allow) ≜
      let γ = new tape in let kr = ref None in
      -- the initiator
      ( λ (). let key = g^rand(γ) in kr := Some key;
              notify true; if allow true then Some key else None
      -- the responder
      , λ (). if allow false then (let k = !kr in notify false; k) else None )

    S_DHKE (leak, deliver) ≜
      let sentA, sentB = ref false in let α, β = new tapes in
      -- notify
      ( λ p. (if p then sentA else sentB) := true;
             leak (p, g^rand(if p then α else β))
      -- allow
      , λ p. let d = deliver p in d && !(if p then sentB else sentA) )

    REAL_DHKE ≜ DH_KE ⊳ F_AUTH        IDEAL_DHKE ≜ F_KE ⊳ S_DHKE

The simulator shows the adversary a fake half when a party starts, and
lets a party have the key when the adversary delivers and the peer's fake
half is out. `F_KE` samples the key when the initiator starts, not when
the instance is created: a protocol that uses the key can then couple it
with something that depends on its own input (section 5).

    dhke_security :
      advantage A REAL_DHKE IDEAL_DHKE ≤ advantage (RED_DHKE A) DH_real DH_rand

for environments typed at `Mod Net Keys → 𝔹`. The proof is two equivalences
in the equivalence logic of `eq/` (`REAL ≃ C_DH DH_real ⊳ F_AUTH` and
`C_DH DH_rand ⊳ F_AUTH ≃ IDEAL`) and the reduction step.

Notes from the proof:

* The simulator must record that a party has started *before* it leaks
  the fake half. With the other order an adversary that runs the responder
  from inside the leak callback distinguishes the two worlds. Earlier
  sketches of the simulator had this bug; the proof found it.
* `DH_KE`, `F_KE` and `S_DHKE` allocate presampling tapes, as proof
  devices.

## 5. A secure channel, and its composition with DHKE (mechanised)

Files: `channel.v`, `channel_proof.v`, `channel_typing.v`,
`channel_dhke.v`.

A one-time secure channel: the sender masks its message with the key and
sends it over a one-way authenticated channel.

    F_OAUTH (leak, deliver) ≜
      let box = ref None in
      -- send
      ( λ x.  box := Some x; leak x
      -- recv
      , λ (). if deliver () then !box else None )

    CHAN ((keyA, keyB), (send, recv)) ≜
      -- the sender
      ( λ m.  match keyA () with None ⇒ () | Some k ⇒ send (m · k)
      -- the receiver
      , λ (). match keyB () with None ⇒ None
              | Some k ⇒ match recv () with None ⇒ None
                                          | Some c ⇒ Some (c · k⁻¹) )

    F_CHAN (notify, allow) ≜
      let box = ref None in
      -- the sender
      ( λ m.  box := Some m; notify ()
      -- the receiver
      , λ (). if allow () then !box else None )

    S_CHAN ((notify, allow), (leak, deliver)) ≜
      let started, sent = ref false in let ρ = new tape in
      -- notify
      ( λ (). started := true; notify true;
              if allow true then (sent := true; leak (g^rand(ρ))) else ()
      -- allow
      , λ (). if allow false then
                let s = !started in notify false;
                if s then (let d = deliver () in d && !sent) else false
              else false )

Interfaces: `F_OAUTH : Mod ONet OEp`, `CHAN : Mod (Keys × OEp) SChan`,
`F_CHAN : Mod CAdv SChan`, `S_CHAN : Mod (Ctl × ONet) CAdv`. The simulator
plays both parties of the key exchange towards the adversary and shows it
a random group element as the ciphertext.

    chan_security :
      advantage A (CHAN ⊳ (F_KE ⊗ F_OAUTH)) (F_CHAN ⊳ S_CHAN) ≤ 0

for environments typed at `Mod (Ctl × ONet) SChan → 𝔹`: one equivalence in
the logic of `eq/`. When the sender starts, the key `g^c` is coupled with
the simulator's ciphertext `g^r` along the bijection `r ↦ log(m · g^c)`.

**The composition.**

    chan_dhke_security :
      advantage A (CHAN ⊳ (REAL_DHKE ⊗ F_OAUTH))
                  (F_CHAN ⊳ (S_CHAN ⊳ (S_DHKE ⊗ id)))
        ≤ advantage (RED_DHKE (λ v. A (CHAN ⊳ (v ⊗ F_OAUTH))))
                    DH_real DH_rand

for environments typed at `Mod (Net × ONet) SChan → 𝔹`. It is
`uc_composition` with `Rw = REAL_DHKE ⊗ F_OAUTH`, `F = F_KE ⊗ F_OAUTH`,
`S = S_DHKE ⊗ id`, `ρ = CHAN`, `S' = S_CHAN`, `G = F_CHAN`:

* the second hypothesis is `chan_security`;
* the first, "DHKE beside the authenticated channel", is `dhke_security`
  for the environment `λ v. A (v ⊗ F_OAUTH)`, followed by interchange;
* the typing hypotheses are the typings of `S_DHKE`, `F_KE`, `F_OAUTH`,
  `CHAN`, `S_CHAN`, `F_CHAN` (`dhke_typing.v`, `channel_typing.v`), each
  proved as a self-equivalence in the logic of `eq/`.

The instance is about twenty lines. The DDH reduction it produces is the
one for DHKE, applied to the environment extended by the channel protocol
and the authenticated channel.

Notes from the proofs:

* *Order of effects in the simulator.* `S_CHAN` sets `started` before
  `notify true` and `sent` before `leak`, and reads `started` before
  `notify false` and `sent` after `deliver`, because the real programs
  write and read the key and the ciphertext at those points. The adversary
  can run the other party from inside any of these callbacks, so each
  order is observable.
* *Write-once state.* The key (real) and the message (ideal) are written
  once. The invariant keeps them as persistent points-to; the receiver
  holds the key it has read and learns by agreement that the ciphertext it
  reads later was made with that key.
* *Typing the components.* Two rules were added to `eq_modules.v`: calling
  an affine port while keeping a frame (`eq_call_frame_aff`; `CHAN` holds
  the endpoint while it asks for the key), and calling an operation
  without a frame at the operation's own row (`eq_call`; the simulators'
  operations are multi-use, so their state lives in an invariant and
  nothing needs to be kept across a call).
* The typings are the largest part of the work (about 470 lines for six
  components) and are routine. A syntactic type system with tapes and the
  group type would produce them.

## 6. Alternatives considered

**A. Keep `uc/`, repair it.** Index an interface by a single row so that a
product of interfaces is an interface, and add an identity. This would
give one composition theorem while keeping a handler in every component.
Not chosen: it keeps the per-component labels, exhaustion steps and
client-taking shape, none of which do any work (section 1).

**B. Global effects, every component a handler** (the paper's Section 2).
A component is `λ f. handle f () with …` over globally named effects;
composition is handler nesting, and side functionalities need no wiring
because unhandled effects propagate. Not chosen:
* two instances of one functionality in one world share its names, so
  definitions need label parameters or session tags plus distinctness
  hypotheses;
* the handlers are still tail-resumptive: it buys implicit wiring, not
  control.

**C. Closures for honest ports, global effects for the adversarial
interface.** A functionality performs `do leak`; a simulator is a
tail-resumptive handler for the ideal interface, attached around each
port (`S ▷ M`). This was mechanised in full and then removed. What it
showed:
* *Global names do not fit the language.* A label exists only after an
  `effect` step and label substitution does not enter values. Components
  therefore had to be open expressions run under a prelude
  `effect s₁ (… (Z W))` over a fixed universe of names. With that came
  name-resolution lemmas, `is_closed_expr` premises on every component,
  and typing "for all label resolutions". None of it concerns the
  protocols.
* *Moving a simulator past a protocol is a real lemma.* With the handler
  at the port, its clause runs inside the protocol's evaluation context on
  one side and outside on the other. That they agree is a free theorem of
  the protocol's row polymorphism, obtained by instantiating the row with
  a single entry whose left labels are the real left labels, whose right
  labels are the ideal label and the real right labels, and whose theory
  pairs "the caught continuation applied to the clause call" with "the
  port about to perform the ideal effect". It was proved in both
  directions (about 650 lines), and it forces the simulator's handler to
  be the framework's fixed `k (c x)`.
* The resulting theorem worked, at about four times the size of
  `modules.v`, with bespoke typing premises.

**D. First-class effect names.** They would let components be closed
values that mention effects. Not chosen: the semantic model would be easy,
but the syntactic type system would need label variables in types and
rows, singleton label types and a scoping discipline, i.e. a different
type system from the one the development extends. And they are not
needed: only the environment handles effects, everything else only
performs, and the ability to perform, `λ x. do l x`, is already a
first-class value with an ordinary row-polymorphic type. That observation
is the present design.

**E. The simulator's handler encloses the client.** A scenario is a
function of its client and the simulator's handler wraps the whole client
(the shape of `uc/`'s `func_comp`). It allows simulators that hold a
continuation. Not chosen for now: no case study needs such a simulator,
and it brings the client-taking shape back.

**What the present design gives up.**
* "The simulator is a handler" is no longer literal. A simulator is
  tail-resumptive by construction; the handler reading is a presentation
  (justified by the lemma of alternative C).
* A side functionality's adversarial operations are threaded explicitly
  through the simulator (`S ⊗ id`); global effects gave that for free. In
  the channel over DHKE this cost one lemma (`dhke_beside_oauth`, about
  twenty-five lines) and the interchange law.
* Active corruption needs an explicit knot: the simulator needs the
  functionality's corrupted port and the functionality needs the
  simulator's operations (section 8).

## 7. Status

| File | Contents | State |
|---|---|---|
| `modules.v` | `Mod`, `⊳`, `⊗`, identity; typing, associativity, interchange; environment extensions; `uc_composition` | proved |
| `eq_modules.v` | rules of the `eq/` logic for modules: calling ports and operations, self-equivalence to typing | proved |
| `dhke.v` | DHKE components, interfaces, `dhke_secure` | definitions |
| `dhke_proof.v` | `dhke_security` | proved |
| `dhke_typing.v` | typings of `F_KE`, `S_DHKE` | proved |
| `channel.v` | channel components, interfaces, `chan_secure` | definitions |
| `channel_proof.v` | `chan_security` | proved |
| `channel_typing.v` | typings of `F_OAUTH`, `CHAN`, `F_CHAN`, `S_CHAN` | proved |
| `channel_dhke.v` | `chan_dhke_security`: the channel over DHKE by `uc_composition` | proved |

No admits. `Print Assumptions chan_dhke_security` lists only the classical
axioms of the reals library, functional and propositional extensionality
and indefinite description; the group is a `clutch_group` instance.

Not done: the typings of `F_AUTH` and `DH_KE` (not needed: the composition
theorem assumes nothing about the real module); the other case studies.

## 8. The other case studies in this style (sketches)

**AUTH from one-time MACs.** `AUTH : Mod RawNet Eps` tags and verifies
with two one-time MAC instances; `S_AUTH : Mod RawNet Net` tags the leaked
message with an ideal MAC and delivers iff the adversary injects exactly
the tagged pair. Affine endpoints remove the `tagged`, `verdict`, `dec`
and `res` state. Bound `2/q`.

**Two-party addition with aggregator.** Messages to the aggregator are
operations of the adversarial interface; `π_ADD : Mod (SChan × Agg) Add`.

**Three-party addition, passive corruption.** `party` and `leaky` stay as
in `examples/secure_add3`; the corrupt party's leak is an adversarial
operation. Network endpoints are multi-use, hence unrestricted. The
simulator runs its own patched network instance and the three fake
parties. The `started` flags and the "one session per environment call"
mechanism disappear; the environment calls three ports and schedules by
handling the network's `wait`.

**OT, active corruption.** A corrupted party's code is deleted and what it
could use is handed to the adversary: in the real world the environment
gets those ports; in the ideal world the simulator gets the corrupted
party's port of `F_OT` and offers simulated versions of what the party
could call. The simulator and the functionality depend on each other, so
they are tied through a reference:

    let r = ref ⊥ in
    let (corrupt, honest) = F_OT (λ x. !r x) in
    r := S_OT adv corrupt; …

Composition under corruption only layers the honest party's code and
leaves the adversary's ports alone.

## 9. Open points

* A blocking `recv` for `F_AUTH` (loop until the adversary delivers and
  the message is there) would remove the option from its result and the
  `None` branches from the protocols. The same applies to `F_OAUTH` and to
  the key ports.
* `F_OAUTH` duplicates one direction of `F_AUTH`. Instantiating the
  channel's authenticated channel from `F_AUTH` (or from the AUTH protocol
  below) would be a second use of `uc_composition`.
* Component typings are proved by hand (section 5).
* The handler presentation of simulators as a stated theorem.
* Simulators that hold a continuation (alternative E), if a case study
  needs one.
