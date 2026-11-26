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
the bookkeeping references of the existing code. Ports that are
multi-use or handed to the adversary are unrestricted and keep guards.

**Waiting ports block.** A port that waits for something (a message, a
key) returns it, not an option. It calls the adversary and checks whether
the thing is there, and repeats until it is:

    recv () ≜ deliver (); match !box with None ⇒ recv () | Some m ⇒ m

The adversary's operation returns unit: it lets the party go on by
returning, and holds it back by not returning (its handler keeps the
continuation). Protocols therefore have no failure branches. A simulator
blocks in the same way, in step with the real protocol.

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

## 4. Authenticated channels and DHKE (mechanised)

Files: `auth.v`, `auth_typing.v`, `dhke.v`, `dhke_proof.v`,
`dhke_typing.v`.

**One primitive.** The one-way authenticated channel carries one message
from a sender to a receiver; the adversary sees it and decides when it is
delivered. The two-way channel is two of them side by side, one per
direction, A to B first:

    F_OAUTH (leak, deliver) ≜
      let box = ref None in
      -- send
      ( λ x. box := Some x; leak x
      -- recv
      , rec recv (). deliver ();
                     match !box with None ⇒ recv () | Some x ⇒ x )

    F_AUTH ≜ F_OAUTH ⊗ F_OAUTH

    F_OAUTH : Mod ONet OEp        F_AUTH : Mod (ONet × ONet) (OEp × OEp)

The typing of `F_AUTH` is the typing of the tensor. Its adversary has a
`leak` and a `deliver` per direction; no operation takes a party tag.

**DHKE.** The initiator is `#true`, the responder `#false`.

    DH_KE ((sendAB, recvAB), (sendBA, recvBA)) ≜
      let α, β = new tapes in
      -- the initiator
      ( λ (). let a = rand(α) in sendAB (g^a); let B = recvBA () in B^a
      -- the responder
      , λ (). let A = recvAB () in let b = rand(β) in sendBA (g^b); A^b )

    F_KE (notify, allow) ≜
      let γ = new tape in let kr = ref None in
      -- the initiator
      ( λ (). let key = g^rand(γ) in kr := Some key;
              notify true; allow true; key
      -- the responder
      , rec resp (). allow false;
                     match !kr with None ⇒ resp ()
                     | Some k ⇒ notify false; k )

    S_DHKE ((leakAB, deliverAB), (leakBA, deliverBA)) ≜
      let sentA, sentB = ref false in let α, β = new tapes in
      -- notify
      ( λ p. if p then (sentA := true; leakAB (g^rand(α)))
                  else (sentB := true; leakBA (g^rand(β)))
      -- allow
      , λ p. if p then (rec wait (). deliverBA ();
                                     if !sentB then () else wait ()) ()
                  else (rec wait (). deliverAB ();
                                     if !sentA then () else wait ()) () )

    REAL_DHKE ≜ DH_KE ⊳ F_AUTH        IDEAL_DHKE ≜ F_KE ⊳ S_DHKE

The simulator shows the adversary a fake half when a party starts, and
lets a party have the key once the adversary has delivered and the peer's
fake half is out. `F_KE` samples the key when the initiator starts, not
when the instance is created: a protocol that uses the key can then couple
it with something that depends on its own input (section 5). Its responder
waits until the key is there.

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
* The waiting loops are related by Löb induction. The channel's `recv`
  (real) runs against the simulator's `allow` (ideal): both call `deliver`
  and then read a location, and the invariant says the two locations are
  set together. The rule `eq_pures_lr` (a pure step on both sides) gives
  the later that the induction needs.

## 5. A secure channel, and its composition with DHKE (mechanised)

Files: `channel.v`, `channel_proof.v`, `channel_typing.v`,
`channel_dhke.v`.

A one-time secure channel: the sender masks its message with the key and
sends it over a one-way authenticated channel, a third instance of
`F_OAUTH` (section 4).

    CHAN ((keyA, keyB), (send, recv)) ≜
      -- the sender
      ( λ m.  let k = keyA () in send (m · k)
      -- the receiver
      , λ (). let k = keyB () in let c = recv () in c · k⁻¹ )

    F_CHAN (notify, allow) ≜
      let box = ref None in
      -- the sender
      ( λ m. box := Some m; notify ()
      -- the receiver
      , rec recv (). allow ();
                     match !box with None ⇒ recv () | Some m ⇒ m )

    S_CHAN ((notify, allow), (leak, deliver)) ≜
      let started, sent = ref false in let ρ = new tape in
      -- notify
      ( λ (). started := true; notify true; allow true;
              sent := true; leak (g^rand(ρ))
      -- allow
      , λ (). (rec wait (). allow false;
                            if !started then () else wait ()) ();
              notify false;
              (rec wait (). deliver ();
                            if !sent then () else wait ()) () )

Interfaces: `CHAN : Mod (Keys × OEp) SChan`,
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

for environments typed at `Mod (Net × ONet) SChan → 𝔹`, where
`Net = ONet × ONet`: the real world has three one-way channels. It is
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
  `notify true` and `sent` before `leak`, and reads `started` after
  `allow false` and `sent` after `deliver`, because the real programs
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
* The typings are the largest part of the work (about 500 lines for six
  components) and are routine. A syntactic type system with tapes and the
  group type would produce them.

## 6. Oblivious transfer with a corrupted receiver (mechanised)

Files: `ot.v`, `ot_arith.v`, `ot_proof.v`. The protocol is the one of `examples/ot`
(1-out-of-2 OT in the CRS model); the choice bit `b` selects `m_b`.

**Corruption.** A corrupted party's code is absent and the adversary plays
it. Each corruption case is written directly, as in `examples/ot` and as
is usual in mechanisations; it is not derived from an honest protocol.
What the corrupted party would have used becomes part of the adversarial
interface:

* *Network.* A channel with a corrupted end adds nothing to what the
  adversary can do, so the honest party talks to the adversary: `recv`
  returns the corrupted party's message (the adversary blocks by not
  returning), `send` takes the reply. There is no `F_OAUTH`.
* *Functionality.* The functionality asks the adversary for the corrupted
  party's input and hands it that party's output, through two adversarial
  operations.

A simulator is then an ordinary module from the real adversarial
interface to the ideal one, the ideal world is `F ⊳ S`, and there is no
mutual dependency between simulator and functionality.

    F_CRS publish ≜
      let crs = (g^sample, g^sample, g^sample, g^sample) in    -- (h1, h0, g1, g0)
      publish crs; crs

    OT_S (crs, (recv, send)) ≜
      λ (m0, m1). let (u, v) = recv () in
                  if u = 1 then () else
                  send (enc (g0, h0, u, v) m0, enc (g1, h1, u, v) m1)

    F_OT_R (choose, output) ≜
      λ (m0, m1). let b = choose () in
                  output (if b then m1 else m0)

    S_OT_R (publish, (recv, send)) ≜
      -- a reference string with a trapdoor
      let g1, g0 = g^sample, g^sample in
      let t1, t0 = sample, sample in
      let crs = (g1^t1, g0^t0, g1, g0) in
      publish crs;
      let st = ref None in
      -- choose: take the receiver's message and extract the choice
      ( λ (). let (u, v) = recv () in
              st := Some (u, v); v ≠ u^t0
      -- output: encrypt the chosen message, and a dummy
      , λ m. let (u, v) = !st in
             if u = 1 then () else
             let (m0, m1) = if v = u^t0 then (m, g) else (g, m) in
             send (enc (g0, h0, u, v) m0, enc (g1, h1, u, v) m1) )

    REAL_OT  ≜ OT_S ⊳ (F_CRS ⊗ id)        IDEAL_OT ≜ F_OT_R ⊳ S_OT_R

    Pub    ≜ Crs → 𝟙                       -- pure: called while the module is set up
    RNet θ ≜ (𝟙 -{θ}-> 𝔾 × 𝔾) × ((𝔾 × 𝔾) × (𝔾 × 𝔾) -{θ}-> 𝟙)
    OTAdv θ ≜ (𝟙 -{θ}-> 𝔹) × (𝔾 -{θ}-> 𝟙)
    SPort θ ≜ (𝔾 × 𝔾) -{¡θ}-∘ 𝟙

**Statement** (`ot_security`), for a group of prime order `n`:

    A : AMod (Pub × RNet) SPort → 𝔹   ⊢   advantage A REAL_OT IDEAL_OT ≤ 3/n

**One instance.** `AMod X Y ≜ ∀θ. X θ ⊸ Y θ` is a module that the
environment instantiates once. A statistical bound is spent when the
module is instantiated (here: when the reference string is sampled), so
the statement is false for an environment that may create several
instances; `examples/ot` has the same restriction.

Notes from the proof:

* One proof in the equivalence logic, read in both directions, instead of
  the two refinements of `examples/ot`; the number-theoretic lemmas of
  `examples/ot/ot_bijection.v` are reused, the mirrored ones are not
  needed. The rule that was missing is a coupling along a bijection that
  avoids one value for an error credit (`eq_couple_rand_rand_avoid` in
  `eq_modules.v`).
* The credits: `1/n` for each of `g0`, `g1` not being the unit, `1/n` for
  the two trapdoors being different.
* The two worlds line up call for call: `recv` then `send` on the left,
  `choose` (which calls `recv`) then `output` (which calls `send`) on the
  right. The sender's port is one-shot, so the simulator's state is owned
  by the port and no invariant is needed.
* Typed payloads remove the group-membership checks and their failure
  branches, and there is no handler: the relational proof is about 110
  lines, against 860.
* The arithmetic is factored into `ot_arith.v` as lemmas on group
  elements `g ^+ k` for natural numbers `k`: the trapdoor bijection
  (`trap`, `trap_exp`), the masking of a ciphertext by a dummy (`mask_r`,
  `mask_s`, `mask_fst`, `mask_snd`) and when a key is not degenerate
  (`nondeg_other`, `nondeg_self`). The conversion to the `fin n` of
  `ot_bijection.v` happens inside those lemmas only.

**Composition.** `F_OT_R : Mod OTAdv SPort` is a plain module, so a
protocol `ρ` on the sender's port composes by `uc_composition`; in the
hybrid world the environment plays the corrupted receiver by providing
`choose` and `output`. Two things are needed first:

* `uc_composition` is stated for `Mod`. With a statistical step it has to
  be stated for one-instance modules. The module type should take the
  mode as a parameter, with the operator lemmas and the theorem proved for
  any mode; a statement for `Mod` implies the one for `AMod`.
* For OT reversal on top of this case (Alice, the OT receiver, corrupted),
  Bob samples his mask before he calls the sender port, hence before
  `choose` is called, while the proof couples the mask with a value that
  depends on the choice. A sender port in two phases,
  `λ (). let b = choose () in λ (m0, m1). output …`, lets Bob sample
  afterwards; the real sender already has this shape.

## 7. Alternatives considered

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
* Corruption cases are written one by one; the honest protocol does not
  appear in their statements (section 6).

## 8. Status

| File | Contents | State |
|---|---|---|
| `modules.v` | `Mod`, `AMod`, `⊳`, `⊗`, identity; typing, associativity, interchange; environment extensions; `uc_composition` | proved |
| `eq_modules.v` | rules of the `eq/` logic for modules: calling ports and operations, self-equivalence to typing, coupling with an avoided value | proved |
| `auth.v` | `F_OAUTH`, `F_AUTH ≜ F_OAUTH ⊗ F_OAUTH`, their interfaces | definitions |
| `auth_typing.v` | typings of `F_OAUTH`, `F_AUTH` | proved |
| `dhke.v` | DHKE components, interfaces, `dhke_secure` | definitions |
| `dhke_proof.v` | `dhke_security` | proved |
| `dhke_typing.v` | typings of `F_KE`, `S_DHKE` | proved |
| `channel.v` | channel components, interfaces, `chan_secure` | definitions |
| `channel_proof.v` | `chan_security` | proved |
| `channel_typing.v` | typings of `CHAN`, `F_CHAN`, `S_CHAN` | proved |
| `channel_dhke.v` | `chan_dhke_security`: the channel over DHKE by `uc_composition` | proved |
| `ot.v` | OT components with a corrupted receiver, interfaces, `ot_secure` | definitions |
| `ot_arith.v` | the bijections on exponents the OT proof couples along (trapdoor, ciphertext masking), over natural numbers | proved |
| `ot_proof.v` | `ot_security` | proved |

No admits. `Print Assumptions` of `chan_dhke_security` and of `ot_security` lists only the classical
axioms of the reals library, functional and propositional extensionality
and indefinite description; the group is a `clutch_group` instance.

Not done: the typing of `DH_KE` (not needed: the composition theorem
assumes nothing about the real module); the other case studies.

## 9. The other case studies in this style (sketches)

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

**OT with a corrupted sender.** As section 6, with the receiver's code kept:
the functionality asks the adversary for the two messages, and the bound
is a DDH term plus `2/n` through a reduction that replaces `F_CRS`.

**OT reversal.** `F_TO` from `F_OT` and one authenticated message; see the
notes on composition in section 6.

## 10. Open points

* Blocking ports loop when the adversary returns too early, so an
  adversary that always returns at once makes a party diverge. Both
  worlds diverge alike, and the logic is about partial correctness, so
  the statements are unaffected; a `deliver` that could only return when
  the message is there would need the functionality to hold the party's
  continuation.
* Component typings are proved by hand (section 5).
* `uc_composition` for one-instance modules, and the component typings of
  the OT example, which it needs (section 6).
* The handler presentation of simulators as a stated theorem.
* Simulators that hold a continuation (alternative E), if a case study
  needs one.
