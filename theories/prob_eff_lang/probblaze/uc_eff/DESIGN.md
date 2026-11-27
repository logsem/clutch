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

**Modes.** The module type takes a mode, `ModM m X Y ≜ ∀θ. X θ -[m]-> Y θ`,
with `Mod ≜ ModM MS` and `ModA ≜ ModM OS` (one instance, section 6). The
operator lemmas are proved once for the functions `X θ ⊸ Y θ` at one row
and lifted to either mode; `uc_composition` takes the mode as a parameter,
and all its premises and environments are at that mode. A module is a
one-instance module (`Mod_ModA`), so an environment of `ModA`s is an
environment of `Mod`s, and a bound for every environment of `Mod`s is a
bound for every environment of `ModA`s (`advantage_Mod_ModA`).

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

Files: `ot.v` (the protocol, shared by all cases), `ot_arith.v`,
`ot_corrupted_receiver.v`, `ot_corrupted_receiver_proof.v`. The protocol is the one of `examples/ot`
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

    -- the generator g is a public parameter, fixed in advance
    DDH_real () ≜ let y, x = sample, sample in (g^(y x), g^x, g^y, g)
    DDH_rand () ≜ let y, x, z = sample, sample, sample in (g^z, g^x, g^y, g)

    F_CRS_DH dh publish ≜ let crs = dh () in publish crs; crs    -- crs = (h1, h0, g1, g0)
    F_CRS ≜ F_CRS_DH DDH_rand                                   -- three random elements, g0 = g

    OT_S (crs, (recv, send)) ≜
      λ (). let (u, v) = recv () in
            λ (m0, m1). if u = 1 then () else
                        send (enc (g0, h0, u, v) m0, enc (g1, h1, u, v) m1)

    F_OT_R choose ≜
      λ (). let (b, output) = choose () in
            λ (m0, m1). output (if b then m1 else m0)

    S_OT_R (publish, (recv, send)) ≜
      -- a reference string with trapdoors t0 (for g) and t1 (for g1)
      let g1 = g^sample in
      let t0, t1 = sample, sample in
      let crs = (g1^t1, g^t0, g1, g) in
      publish crs;
      -- the receiver's message, the extracted choice, and the real
      -- sender on that message: the chosen message and a dummy
      λ (). let (u, v) = recv () in
            let b = (v ≠ u^t0) in
            let k = OT_S (crs, (λ (). (u, v), send)) () in
            (b, λ m. k (if b then (g, m) else (m, g)))

    REAL_OT_R  ≜ OT_S ⊳ (F_CRS ⊗ id)        IDEAL_OT_R ≜ F_OT_R ⊳ S_OT_R

    Pub    ≜ Crs → 𝟙                       -- pure: called while the module is set up
    RNet θ ≜ (𝟙 -{θ}-> 𝔾 × 𝔾) × ((𝔾 × 𝔾) × (𝔾 × 𝔾) -{θ}-> 𝟙)
    OTAdv θ ≜ 𝟙 -{¡θ}-∘ (𝔹 × (𝔾 -{¡θ}-∘ 𝟙))     -- one-shot: only F_OT_R calls it
    SPort θ ≜ 𝟙 -{¡θ}-∘ ((𝔾 × 𝔾) -{¡θ}-∘ 𝟙)

The sender's port has two phases: the first fixes the receiver's choice
(`recv`, resp. `choose`), the second takes the messages. A client may then
sample after the choice is fixed; OT reversal needs this (below). This
is a concession to the proof method, not the textbook functionality,
whose sender gives its messages at once; see alternative F (section 7)
for the textbook version and why it is not used. The real protocol has
this shape anyway (the receiver speaks first), and a one-phase client
calls the two phases one after the other.

**Statement** (`ot_r_security`), for a group of prime order `n`:

    A : ModA (Pub × RNet) SPort → 𝔹   ⊢   advantage A REAL_OT_R IDEAL_OT_R ≤ 2/n

**One instance.** `ModA X Y ≜ ∀θ. X θ ⊸ Y θ` (`ModM OS`) is a module that the
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
* The credits: `1/n` for `g1` not being the unit, `1/n` for the two
  trapdoors being different. (With the generator in the reference
  string, as in `examples/ot`, a third `1/n` for `g0 ≠ 1`.)
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
`choose` and `output`. Notes:

* With a statistical step the composition is about one-instance modules:
  `uc_composition` at mode `OS` (section 3). It needs the typings of the
  components at `ModA`; a typing at `Mod` gives one (`Mod_ModA_typed`).

**OT reversal on top (agreed design; statement 1 is mechanised as
`to_s_security` in `ot_rev_corrupted_sender.v`/`ot_rev_corrupted_sender_proof.v`, where the simulator is
named `S_TO_S`).** Reversed OT (TO) from this OT and one message. In the OT, Bob is the sender (honest)
and Alice the receiver (corrupted). In the TO, Alice is the sender with
two bits `(x0, x1)`, Bob the receiver with a choice bit `c`; Alice stays
corrupted. Bob offers `(r, r ⊕ c)` for a random mask `r`; Alice chooses
`s = x0 ⊕ x1`, learns `r ⊕ (s ∧ c)` and sends `m = x0 ⊕ r ⊕ (s ∧ c)`; Bob
outputs `m ⊕ r = x_c`. Alice's code is absent, so her message is an
adversarial operation `recv` (section 6: no `F_AUTH`). Bits go through
the group OT as `gbit b ≜ if b then g else 1`. TO messages are bits:
reversal needs XOR on them.

    TO_R (sport, recv) ≜                      -- Bob
      λ c. let snd = sport () in              -- Alice's OT choice is fixed
           let r = flip () in                 -- the mask
           snd (gbit r, gbit (r ⊕ c));
           let m = recv () in                 -- Alice's message
           m ⊕ r

    F_TO_S input ≜                            -- TO, sender corrupted
      λ c. let (x0, x1) = input () in
           if c then x1 else x0

    HYB_TO_S ≜ TO_R ⊳ (F_OT_R ⊗ id)

    S_TO_S (choose, recv) ≜                   -- (mechanised form)
      λ (). let (s, output) = choose () in    -- Alice's OT choice, x0 ⊕ x1
            let x0 = HYB_TO_S ((λ (). (s, output)), recv) false in
            (x0, x0 ⊕ s)                      -- Bob on the dummy choice outputs x0

    TPort θ ≜ 𝔹 -{¡θ}-∘ 𝔹       ARecv θ ≜ 𝟙 -{θ}-> 𝔹       TOAdv θ ≜ 𝟙 -{¡θ}-∘ 𝔹 × 𝔹

    TO_R : Mod (SPort × ARecv) TPort          F_OT_R ⊗ id : Mod (OTAdv × ARecv) (SPort × ARecv)
    S_TO_S : Mod (OTAdv × ARecv) TOAdv        F_TO_S      : Mod TOAdv TPort

`recv` is not a port of `F_OT_R`; it is passed beside it, so the hybrid
world is `TO_R ⊳ (F_OT_R ⊗ id)`. Statements:

1. Reversal is perfect, for `Mod`:
   `advantage A (TO_R ⊳ (F_OT_R ⊗ id)) (F_TO_S ⊳ S_TO_S) ≤ 0`. The worlds
   line up call for call (`choose`, sample, `output`, `recv`), with the
   one coupling `ρ = r ⊕ (s ∧ c)`. It needs the two-phase sender port:
   `s` is known when Bob samples `r`. For `ModA` by `advantage_Mod_ModA`.
2. `REAL_OT_R ⊗ id` realises `F_OT_R ⊗ id` with `S_OT_R ⊗ id` up to `2/n`,
   from `ot_r_security` by `env_beside_typed` and interchange.
3. By `uc_composition OS`:
   `advantage A (TO_R ⊳ (REAL_OT_R ⊗ id)) (F_TO_S ⊳ (S_TO_S ⊳ (S_OT_R ⊗ id))) ≤ 2/n`.

**OT with a corrupted sender (mechanised, `ot_corrupted_sender.v`, `ot_corrupted_sender_proof.v`;
pseudocode not reviewed before mechanising).** The receiver's code is
kept and the adversary plays the sender: the receiver `send`s its message
to the adversary and `recv`s the reply. The functionality asks the
adversary for the sender's messages when the receiver chooses.

    OT_R (crs, (send, recv)) ≜                -- the receiver
      λ b. let x = sample in
           let (gb, hb) = if b then (g1, h1) else (g0, h0) in
           send (gb^x, hb^x);
           let (e0, e1) = recv () in
           dec x (if b then e1 else e0)        -- dec x (c, d) = d · c^-x

    F_OT_S input ≜ λ b. let (m0, m1) = input () in if b then m1 else m0

    S_OT_S (publish, (send, recv)) ≜
      -- a reference string in decryption mode, trapdoor y
      let y = sample in let x = sample in
      let g1 = g^y in
      publish (g1^x, g^x, g1, g);
      -- input: a receiver's message that opens both slots
      λ (). let a1 = sample in let a0 = a1 · y in
            send (g^a0, h0^a0);                -- = (g1^a1, h1^a1)
            let (e0, e1) = recv () in
            (dec a0 e0, dec a1 e1)

    SNet θ ≜ ((𝔾 × 𝔾) -{θ}-> 𝟙) × (𝟙 -{θ}-> (𝔾 × 𝔾) × (𝔾 × 𝔾))
    OTSAdv θ ≜ 𝟙 -{θ}-> 𝔾 × 𝔾        RPort θ ≜ 𝔹 -{¡θ}-∘ 𝔾

DDH is the textbook assumption for the fixed generator `g`, stated as two
samplers in the shape of a reference string (`DDH_real`, `DDH_rand`
above). The real reference string is a random tuple: `F_CRS` *is*
`F_CRS_DH DDH_rand`. The DDH adversary is the environment with the rest of the real world
around the sampler, `DDH_RED A ≜ λ v. A (OT_R ⊳ (F_CRS_DH v ⊗ id))`.

    A : ModA (Pub × SNet) RPort → 𝔹   ⊢
      advantage A REAL_OT_S IDEAL_OT_S
        ≤ advantage (DDH_RED A) DDH_rand DDH_real + 1/n

Two steps (`ot_s_security`): the DDH advantage, the real module being the
hybrid with `DDH_rand` (`hyb_ddh`, `advantage_reduction_ctx`); with a DDH string the
receiver's `x` is the simulator's `a1` (if `b`) or `a0 = a1 · y` (if not,
coupling `a1 = x / y`, `1/n` for `y ≠ 0`) (`dh_ideal_EQ`). The bound is
that of `examples/ot` less the `1/n` for `g0 ≠ 1`, which the fixed
generator makes unnecessary. New arithmetic in `ot_arith.v`: `trap_mul`
(`c ^ (trap y t · y) = c ^ t` for any `c`) and `expg_mul`.

**OT, both parties honest (mechanised, `ot.v`, `ot_proof.v`).** The
parties are `OT_S` and `OT_R` unchanged: with both honest, their network
operations are the endpoints of two `F_OAUTH` channels (the receiver's
message, then the ciphertexts). The corruption cases are the same code
with an endpoint replaced by the adversary.

    PARTIES_OT (crs, ((send_rs, recv_rs), (send_sr, recv_sr))) ≜
      (OT_S (crs, (recv_rs, send_sr)), OT_R (crs, (send_rs, recv_sr)))
    REAL_OT_H ≜ PARTIES_OT ⊳ (F_CRS ⊗ (F_OAUTH ⊗ F_OAUTH))

    F_OT_H (run_s, run_r) ≜
      let ch = ref false in let mm = ref None in
      ( λ (). let run_s2 = run_s () in           -- sender, first phase
              if !ch then (λ (m0, m1). mm := Some (m0, m1); run_s2 ())
              else loop ()
      , λ b. ch := true; run_r ();               -- receiver
             match !mm with Some (m0, m1) → if b then m1 else m0
                          | None → loop () )

    DUMMY_OT (sport, rport) ≜
      (λ (). let k = sport () in λ (). k (1, 1), λ (). rport false; ())
    S_OT_H ≜ DUMMY_OT ⊳ HYB1_OT_H DDH_real
    OTHAdv θ ≜ (𝟙 -{¡θ}-∘ (𝟙 -{¡θ}-∘ 𝟙)) × (𝟙 -{¡θ}-∘ 𝟙)

**Honest functionalities: the adversary runs a party.** A port records
the party's input and hands control to the adversary with that party's
operation; when it returns, the party is done (UC's delayed output).
The sender's operation returns the operation for its second phase. The
functionality checks its conditions afterwards and never returns a port
that is not yet entitled to: the sender's first phase if the receiver
has not chosen, the receiver's output if the sender has not given its
messages (it diverges instead). The ports block as the real ones do,
and the environment schedules them by handling the network operations
inside the simulator, so the simulator can run a whole party in one
call. The simulator is the textbook one in the CRS model: the real
parties on dummy inputs (choice `false`, messages `(1, 1)`), on a
reference string it chooses in decryption mode. It holds no state and
is typed by composition. (Earlier versions gave the adversary one
`yield` per party and party move, with a simulator that was a state
machine per party, or one operation per network event; see the honest
reversal below for why that was dropped.)

    A : ModA OTHNet OTPorts → 𝔹   ⊢
      advantage A REAL_OT_H IDEAL_OT_H
        ≤ advantage (RED1_OT_H A) DDH_rand DDH_real
          + advantage (RED2_OT_H A) DDH_real DDH_rand
          + advantage (RED2_OT_H (DENV_OT_H A)) DDH_real DDH_rand + 3/n

`DENV_OT_H A ≜ λ v. A (F_OT_H ⊳ (DUMMY_OT ⊳ v))` (as nested `comp_app`).
The steps (`ot_h_security`):

| Step | From → to | Cost |
|---|---|---|
| A | `REAL_OT_H = HYB1_OT_H DDH_rand` → `HYB1_OT_H DDH_real` (decryption mode) | DDH, reduction `RED1_OT_H A` |
| B | `HYB1_OT_H DDH_real` → `HYB2_OT_H DDH_real` | `1/n` (`y ≠ 0`) |
| C | `HYB2_OT_H DDH_real` → `HYB2_OT_H DDH_rand` | DDH, reduction `RED2_OT_H A` |
| E | `HYB2_OT_H DDH_rand` → `F_OT_H ⊳ (DUMMY_OT ⊳ HYB2_OT_H DDH_rand)` | `1/n` (`c ≠ p q`) |
| C⁻¹ | → `F_OT_H ⊳ (DUMMY_OT ⊳ HYB2_OT_H DDH_real)` | DDH, reduction `RED2_OT_H (DENV_OT_H A)` |
| B⁻¹ | → `F_OT_H ⊳ (DUMMY_OT ⊳ HYB1_OT_H DDH_real) = IDEAL_OT_H` | `1/n` |

C⁻¹ and B⁻¹ are steps C and B for the environment `DENV_OT_H A`, typed
by `env_under_typed` with the typings of `F_OT_H` and `DUMMY_OT`
(`advantage_reduction_ctx` twice, `under_dummy_adv`; `advantage_sym` for
the direction). Step A is not repeated: the simulator keeps the
decryption-mode string, the textbook choice. A simulator running the
real protocol unchanged (`DUMMY_OT ⊳ REAL_OT_H`) would cost a fourth DDH
term.

`HYB2_OT_H dh` is the parties with a decryption-mode string they sample
themselves (they need its `y`), whose receiver's message and ciphertexts
are built from one tuple of `dh`, `(C, B, A) = (g^c, g^q, g^p)`, taken
when the receiver chooses: `u = A`, `v = u^x`, slot `i` is
`((B^α_i · g^β_i)^(y_i), m_i · C^α_i · A^β_i)`; the receiver outputs the
sender's `m_b` from a shared reference. Every sample is coupled with one
taken at the same point on the other side:

* B: the receiver's `z` with `p = y_b z`; the sender's `s_i` with `α_i`
  and `r_i` with `β_i = r_i + (x − q) s_i`; the tuple's `q` on the right
  only. The receiver's output is its decryption, `m_b` by correctness.
* E: the receiver's message `(A, A^x)` does not depend on its choice;
  the tuple is the same on both sides, `c` avoiding `p q`; slot `i` of
  the real sender against the dummy one: `α_i ↦ α_i + δ_i`,
  `β_i ↦ β_i − q δ_i` for `δ_i = log m_i / (c − p q)`, so the
  ciphertexts of `m_i` and of `1` are the same. The invariants are one
  per channel box, as in the honest reversal.

The proofs of B and E have one invariant per channel box, "not yet
sent on both sides" or "sent, with related values", whose writer holds
half of the right-hand points-to as its "not yet" token; the hybrid's
tuple and messages are owned by their writer and persistent once
written. New rules: a one-sided `rand` (`eq_randU_l/r`) and a one-sided
`rand` avoiding a value for an error credit (`eq_rand_avoid_l/r`, ported
from approxis), in the core logic; affine couplings of exponents in
`ot_arith.v` (`gexp`, `aff`). Stdlib's `ring` does not apply to `'F_n`
(its operators come through several canonical instance paths), so the
field identities are proved by rewriting.

**OT reversal, the other two cases (mechanised; `ot_rev.v` has the
parties and the honest case, `ot_rev_corrupted_receiver.v` Bob corrupted,
each with its `_proof.v`; pseudocode not reviewed before mechanising).** The
parties are the same code in all three cases; a corrupted party's code is
absent and its network operations go to the adversary.

*Bob corrupted* (`to_r_security`, perfect, for `Mod`). Alice is `TO_S` on
the OT with a corrupted sender, and her message goes to the adversary:

    TO_S (rport, send) ≜ λ (x0, x1). let z = ungbit (rport (x0 ⊕ x1)) in
                                     send (x0 ⊕ z)            -- ungbit u = (u = g)
    F_TO_R choose ≜ λ (x0, x1). let (c, output) = choose () in
                                output (if c then x1 else x0)
    S_TO_R (input, send) ≜
      λ (). let (u0, u1) = input () in        -- Bob's OT messages
            (ungbit u0 ⊕ ungbit u1,           -- his choice
             λ x. HYB_TO_R ((λ (). (u0, u1)), send) (x, x))   -- Alice on (x_c, x_c)

    HYB_TO_R ≜ TO_S ⊳ (F_OT_S ⊗ id)   IDEAL_TO_R ≜ F_TO_R ⊳ S_TO_R
    TSPort θ ≜ 𝔹 × 𝔹 -{¡θ}-∘ 𝟙   ASend θ ≜ 𝔹 -{θ}-> 𝟙
    TORAdv θ ≜ 𝟙 -{¡θ}-∘ (𝔹 × (𝔹 -{¡θ}-∘ 𝟙))

Whatever group elements Bob sends, Alice's message is
`x0 ⊕ ungbit u_s = x_c ⊕ r` for `r = ungbit u0`, `c = r ⊕ ungbit u1`,
which is what Alice on `(x_c, x_c)` sends: no sample, no coupling, a case
analysis on the bits.

**Simulators with a corrupted party: the real honest party on
synthesised inputs.** As in the honest cases, a simulator runs the
honest party's real code; with a party corrupted it also extracts that
party's input for the functionality, and feeds the honest party inputs
built from what the functionality returns:

| Case | Runs | On | Extracts |
|---|---|---|---|
| OT, receiver corrupted (`S_OT_R`) | `OT_S` | `(m_b, g)` or `(g, m_b)` | `b`, with the trapdoor `t0` |
| reversal, Alice corrupted (`S_TO_S`) | `HYB_TO_S` | Bob's choice `false` | `x1 = x0 ⊕ s` |
| reversal, Bob corrupted (`S_TO_R`) | `HYB_TO_R` | Alice's bits `(x_c, x_c)` | `c = ungbit u0 ⊕ ungbit u1` |

The simulator reads the corrupted party's message itself and gives the
honest party a network operation that replays it, so the adversary sees
each call once and the simulator keeps no state. The functionality's
operation for the corrupted party is one-shot and returns the operation
for the rest (`OTAdv`, `TORAdv`), so the simulator can call the honest
party's one-shot port from it; the simulators are typed through the
typings of the parties (`val_typed_eq`, module call at `¡⟨⟩ ≤ ¡θ`). The
OT with a corrupted sender is the exception: extracting `m1` needs the
receiver's secret, which `OT_R` keeps, so `S_OT_S` is the receiver's
code on the dummy choice with the second slot opened by the trapdoor.

*Both honest* (`to_h_security`, perfect, for `Mod`). Alice and Bob
on `F_OT_H` and an `F_OAUTH` from Alice to Bob:

    PARTIES_TO ((sport, rport), (send, recv)) ≜
      (TO_S (rport, send), TO_R (sport, recv))
    HYB_TO_H ≜ PARTIES_TO ⊳ (F_OT_H ⊗ F_OAUTH)

    F_TO_H (run_a, run_b) ≜
      let xs = ref None in
      ( λ x. xs := Some x; run_a ()                      -- Alice
      , λ c. run_b ();                                   -- Bob
             match !xs with Some (x0, x1) → if c then x1 else x0
                          | None → loop () )

    DUMMY_TO (alice, bob) ≜ (λ (). alice (false, false), λ (). bob false; ())
    S_TO_H ≜ DUMMY_TO ⊳ HYB_TO_H

    TOHAdv θ ≜ (𝟙 -{¡θ}-∘ 𝟙) × (𝟙 -{¡θ}-∘ 𝟙)

A party's port records its input and hands control to the simulator for
the whole of that party's run (UC's delayed output); Bob's port returns
`x_c` only if Alice has given her bits, and otherwise never returns. The
simulator is the textbook one: the real parties on dummy inputs. Its
parties block where the real ones do, on its own OT and channel, whose
adversarial operations are the simulator's; the environment schedules
them by handling those operations, so no component holds a continuation
and the simulator keeps no state of its own. Its typing is that of the
hybrid and `DUMMY_TO`. The operations `run_a`, `run_b` are one-shot:
only the functionality calls them, once each.

The proof relates the real run with the dummy run. Both sides run the
same party code against the same OT and channel, so their positions line
up; the invariants are one per location that one party writes once
(`ch` and `mm` of the OT, `box` of the channel), each "not yet written on
both sides" or "written with related values", with the writer's
half points-to as its "not yet" token. Bob's mask is coupled with the
dummy Bob's along `ρ = x0 ⊕ r ⊕ (s ∧ c)`, so that the dummy Alice sends
Alice's message: when Bob samples, Alice has chosen in the OT, so the
functionality holds her bits. The invariants quantify over the values in
the heap, with a pure condition on them (`mm_ok`, `box_ok`), since an
existential bit under `gbit` is not found by unification.

*Why not a functionality that yields per network move.* The first
version gave the simulator one operation per party, `yield_a`/`yield_b`,
called wherever the real party calls the network; the functionality ran
the wait loops and checked its own flags after each yield (commit
eb4d8b6d). A simulator called back once per move and returning at once
is a state machine: it needed five references (`rho` and four program
counters), and the proof one invariant over four stages that related its
flags with the real world's progress. Effects remove the need: the
environment already suspends a party at any network call, however deep,
so the simulator may run a whole party in one call. The old `uc/`
design would not have helped: its simulators are tail-resumptive
handlers (`k (c x)`), with the same one-step shape. Holding continuations
in the simulator (alternative E) would also give direct-style
simulators, but is not needed here.

**The composition with the real OT (`ot_rev_ot.v`; typings in
`ot_typing.v`, `ot_rev_typing.v`).** For each case, statement 2 is the
OT's realisation beside the interface the reversal adds, from the OT's
security theorem by `env_beside_typed` and `tens_interchange`; statement
3 is `uc_composition OS` with the reversal's perfect realisation, which
is stated for `Mod` and turned into one for `ModA` by
`advantage_Mod_ModA`. The environment instantiates the composed module
once (`ModA`), as the OT statements require.

| case | statement 3 | beside the OT | simulator | bound |
|---|---|---|---|---|
| Alice corrupted | `to_s_ot_security` | `id` (Alice's message, `ARecv`) | `S_TO_S ⊳ (S_OT_R ⊗ id)` | `2/n` |
| Bob corrupted | `to_r_ot_security` | `id` (Alice's message, `ASend`) | `S_TO_R ⊳ (S_OT_S ⊗ id)` | DDH + `1/n` |
| both honest | `to_h_ot_security` | `F_OAUTH` carrying a bit | `S_TO_H ⊳ (S_OT_H ⊗ id)` | three DDH terms + `3/n` |

The DDH reductions get the environment with the reversal's parties
composed in front and the identity or the channel beside, as in
`chan_dhke_security`.

Two generalisations were needed for this, and nothing in the existing
proofs changed:

* `F_OAUTH` carries a bit in the honest reversal, so its typing is
  proved for any first-order message type (`F_OAUTH_eq_gen`, over
  `ONetT τ`/`OEpT τ`; `ONet`/`OEp` are the instances at `𝔾`). A
  first-order type is one whose related values are equal and satisfy a
  pure predicate (`eq_ground`, `eq_modules.v`), which can then be kept in
  an invariant; `𝔹`, `𝔾` and products of them are first-order.
* Alice and Bob use Alice's message through a persistent adversarial
  operation when the other party is corrupted (`ASend`, `ARecv`), and
  through an affine channel endpoint when both are honest. Their typings
  are proved once for any interface that can be used as a one-shot
  operation (`TO_S_eq_gen`, `TO_R_eq_gen`); a persistent operation can
  (`eq_arr_aff`).

The state of `F_OT_H` and `F_TO_H` is a flag or a box per reference,
each in its own non-atomic invariant, with rules that open, access and
close in one step (`eq_na_load_bool`, `eq_na_store_bool`,
`eq_na_load_box`, `eq_na_store_box`). `S_OT_H` and `S_TO_H` are typed by
composition.

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

**F. The textbook OT functionality, with a one-phase sender port.** This
is the right formulation: the sender gives `(m0, m1)` at once, and in OT
reversal Bob samples his mask `r` first, as on paper. The paper proof is
an independence argument: `r` is uniform and nothing the adversary sees
depends on it until Alice receives `r ⊕ (s ∧ c)`. The logic has no rule
for it:
* A coupling has to be complete before a call to the adversary: in the
  model (`logic.v`, `rel`/`kwp_pre`/`obs_refines`) the handling context
  is abstract, so neither side can be stepped past an effect, and a
  `rand` before the call cannot be coupled with a `rand` after it. Only
  tapes carry presampled values across the call.
* Even with a tape, the bijection is fixed when the earlier sample is
  taken. The one needed, `ρ = r ⊕ (s ∧ c)`, depends on the adversary's
  later answer `s`. The identity coupling fails when `s = c = 1`; a
  simulator that outputs `ρ ⊕ s` fails when `c = 0` (it does not know
  `c`); coupling `r` with two tapes, one per `s`, is not a coupling (a
  uniform bit against a uniform pair).

What would make it provable is a rule that moves a sample past a call to
the adversary that does not receive it,

    let r = flip () in let s = op () in K   ≈   let s = op () in let r = flip () in K

valid for one-shot rows `¡θ` (it is false if a continuation can be
resumed twice: both resumptions would share `r`). It needs either
prophecy-like reasoning about the adversary's answers or a semantic
independence argument at the level of `lim_exec`, where "resumes at most
once" first has to be expressed. Not done for now; the two-phase port
(section 6) gives the coupling the information it lacks. Open point in
section 10.

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
* The OT sender's port has two phases instead of the textbook one
  (alternative F).

## 8. Status

| File | Contents | State |
|---|---|---|
| `modules.v` | `ModM m` with `Mod`, `ModA`; `⊳`, `⊗`, identity; typing, associativity, interchange; environment extensions, for either mode; `uc_composition` for either mode; `advantage_Mod_ModA` | proved |
| `eq_modules.v` | rules of the `eq/` logic for modules: calling ports and operations, self-equivalence to typing, coupling with an avoided value, first-order types, flags and boxes in invariants | proved |
| `auth.v` | `F_OAUTH`, `F_AUTH ≜ F_OAUTH ⊗ F_OAUTH`, their interfaces | definitions |
| `auth_typing.v` | typings of `F_OAUTH` (for any first-order message type), `F_AUTH` | proved |
| `dhke.v` | DHKE components, interfaces, `dhke_secure` | definitions |
| `dhke_proof.v` | `dhke_security` | proved |
| `dhke_typing.v` | typings of `F_KE`, `S_DHKE` | proved |
| `channel.v` | channel components, interfaces, `chan_secure` | definitions |
| `channel_proof.v` | `chan_security` | proved |
| `channel_typing.v` | typings of `CHAN`, `F_CHAN`, `S_CHAN` | proved |
| `channel_dhke.v` | `chan_dhke_security`: the channel over DHKE by `uc_composition` | proved |
| `ot.v` | OT: the protocol (`F_CRS`, `OT_S`, `OT_R`, `enc`, `dec`), the DDH samplers and `F_CRS_DH`; both honest: `F_OT_H` (delegating), `S_OT_H ≜ DUMMY_OT ⊳ HYB1_OT_H DDH_real`, `REAL_OT_H`, `IDEAL_OT_H`, hybrids, reductions, `ot_h_secure` | definitions |
| `ot_proof.v` | `ot_h_security` (three DDH terms + `3/n`) | proved |
| `ot_eq.v` | the OT values in the eq logic (`eq_crs`, `eq_pair`, `eq_ctxts`, `eq_lift_ctxts`) and the `couple_along` tactics, shared by the OT proofs | proved |
| `ot_arith.v` | the bijections on exponents the OT proofs couple along (trapdoor, ciphertext masking), over natural numbers | proved |
| `ot_corrupted_receiver.v` | `F_OT_R`, `S_OT_R`, `REAL_OT_R`, `IDEAL_OT_R`, `ot_r_secure` | definitions |
| `ot_corrupted_receiver_proof.v` | `ot_r_security` (`2/n`) | proved |
| `ot_corrupted_sender.v` | `F_OT_S`, `S_OT_S`, the reduction `DDH_RED`, `ot_s_secure` | definitions |
| `ot_corrupted_sender_proof.v` | `ot_s_security` (DDH + `1/n`) | proved |
| `ot_rev.v` | OT reversal: the parties `TO_R`, `TO_S`, bits; both honest: `F_TO_H` (delegating), `S_TO_H ≜ DUMMY_TO ⊳ HYB_TO_H`, `to_h_secure` | definitions |
| `ot_rev_proof.v` | `to_h_security` (perfect) | proved |
| `ot_rev_corrupted_sender.v` | Alice corrupted: `F_TO_S`, `S_TO_S`, `to_s_secure` | definitions |
| `ot_rev_corrupted_sender_proof.v` | `to_s_security` (perfect) | proved |
| `ot_rev_corrupted_receiver.v` | Bob corrupted: `F_TO_R`, `S_TO_R`, `to_r_secure` | definitions |
| `ot_rev_corrupted_receiver_proof.v` | `to_r_security` (perfect) | proved |
| `ot_typing.v` | typings of `F_OT_R`, `S_OT_R`, `F_OT_S`, `S_OT_S`, `F_OT_H`, `DUMMY_OT`, `OT_S`, `OT_R`, `PARTIES_OT`, `F_CRS_DH DDH_real`, `HYB1_OT_H DDH_real`, `S_OT_H` | proved |
| `ot_rev_typing.v` | typings of `TO_S`, `TO_R` (for any one-shot interface to Alice's message), `PARTIES_TO`, `F_TO_S`, `HYB_TO_S`, `S_TO_S`, `F_TO_R`, `HYB_TO_R`, `S_TO_R`, `F_TO_H`, `DUMMY_TO`, `HYB_TO_H`, `S_TO_H` | proved |
| `ot_rev_ot.v` | the reversal on the real OT, three cases: `to_s_ot_security`, `to_r_ot_security`, `to_h_ot_security` by `uc_composition OS` | proved |
| `links.v` | two-way modules `ModL`, `link` (lazy import from above), typing, associativity, environment extensions, `uc_composition_link`, for either mode; embedding of one-way modules, `realises_embed`; section 11 | proved |

No admits. `Print Assumptions` of `chan_dhke_security`, `ot_r_security` and the three theorems of `ot_rev_ot.v` lists only the classical
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

**OT with a corrupted sender, OT with both honest, OT reversal.** Section 6.

## 10. Open points

* Blocking ports loop when the adversary returns too early, so an
  adversary that always returns at once makes a party diverge. Both
  worlds diverge alike, and the logic is about partial correctness, so
  the statements are unaffected; a `deliver` that could only return when
  the message is there would need the functionality to hold the party's
  continuation.
* Component typings are proved by hand (section 5).
* The handler presentation of simulators as a stated theorem.
* Simulators that hold a continuation (alternative E), if a case study
  needs one.
* A rule that moves a sample past an adversary call that does not
  receive it, for one-shot rows. With it, OT could have the textbook
  one-phase sender port and OT reversal the textbook client
  (alternative F).

## 11. Two-way interfaces and linking (`links.v`)

**Why.** In the present design every boundary carries operations one
way, so a simulator can only answer the functionality's requests; it
cannot call into the functionality when the adversary decides (adaptive
corruption, an adversary reading a bulletin board, a ledger). That needs
operations in both directions across a boundary, and linking with cycles.

**Interfaces.** Modules are arranged in a stack (protocol above
functionality above simulator), and a boundary `X` between two of them
carries `X.up` (offered by the component below to the one above: ports,
the adversary's operations offered to a module) and `X.down` (offered by
the component above to the one below: ports the adversary may call,
callbacks). OCaml links by name; our modules are values without names,
so the split into up and down is how a link says what is connected to
what. In an OCaml-like notation a module from `X` (below) to `Y` (above)
is a functor whose argument for the module above is lazy:

    module M (Below : X.up) (Above : unit -> Y.down) : sig
      val down : X.down            (* offered below, available at once *)
      val init : unit -> Y.up      (* the rest of the set-up *)
    end

    ModL m X Y ≜ ModM m (X.up × (𝟙 → Y.down)) (X.down × (𝟙 ⊸ Y.up))

One-way modules are the case `X.down = Y.down = 𝟙`. In category terms
this is the Int construction over the modules of section 3.

**Linking** `g ∘ f` (f below, g above) is a recursive module group,
`module rec F = f (X_up) (fun () -> G.down) and G = g (F.init ()) (Z_down)`,
implemented as OCaml implements `module rec`: `f` receives a placeholder
for `G.down`, a reference, filled as soon as `G.down` exists. Looking it
up before that diverges (OCaml raises `Undefined_recursive_module`).

    link g f (x_up, z_down) =
      let r = ref None in
      let (x_down, f_init) = f (x_up, fun () -> get r) in
      (x_down, fun () -> let y_up = f_init () in
                         let (y_down, g_init) = g (y_up, z_down) in
                         r := Some y_down; g_init ())

**Why the import from above is lazy.** A first version passed `Y.down`
itself, as a stand-in bundle that looks each operation up when called (a
proxy). The language cannot build such a bundle generically, so every
interface needed its own proxy, and the composition theorem one proxy
hypothesis per internal boundary. Passing the look-up function instead
removes them; a module calls `above ()` before using the module above.

**Why two stages (`down` before `init`).** With one stage, the time at
which a placeholder is filled depends on the nesting: in `(h ∘ g) ∘ f`
the placeholder for `g`'s down-exports is filled after `h` is set up, in
`h ∘ (g ∘ f)` before. A set-up of `h` that reaches `f`'s placeholder
then diverges in one and not the other, and associativity fails. With
two stages, every placeholder is filled right after its module's first
stage, so all nestings run the same steps in the same order, the order
of one flat `module rec` group, with no condition on what set-ups do.

**The invariant of a link** (`link_inv`): the two references are empty
on both sides, or filled on both sides with related values. A look-up of
an empty placeholder diverges on both sides (`eq_loop`). The interface
offered down across an internal boundary must be persistent (the
invariant keeps `□ ⟪Y.down⟫ y y'`, and it is looked up any number of
times); affine back edges would need a token, not done. This is the only
assumption the composition theorem makes about interfaces.

**Associativity** (`link_assoc`): `h ∘ (g ∘ f)` and `(h ∘ g) ∘ f` run
the same calls in the same order (`f`, `f`'s set-up, `g`, fill `Y`, `g`'s
set-up, `h`, fill `Z`, `h`'s set-up) and differ only in when the
placeholder for `Z` is allocated, a step of one side alone.

**Composition theorem** (`uc_composition_link`), for either mode: as in
section 3, with `∘` for `⊳` and two-way boundaries; the ideal world is
`G ∘ (S' ∘ S)`, in OCaml terms `module rec G' = G (S'') and S'' = S' (S)`.
The proof is the one of `uc_composition`, with `link_assoc` for
associativity and `env_under_link`/`env_over_link` for the environments.

**Modes.** As in section 3: the lemmas are proved at one row
(`link_arr_eq`, `link_assoc_arr`, for `LArr`) and lifted to either mode
(`eq_mod_map2`, `eq_mod_map3`). At one row the modules are affine, so a
module still to be called is carried in the frame of the calls before it.
The internal down-interfaces stay persistent in both modes: an instance
of a one-instance module may still look up the module above any number
of times.

**One-way modules** (`embed`). A one-way module is a two-way module that
offers nothing below and looks nothing up above (down parts `Unit`):
`embed f (x_up, _) = ((), fun () -> f x_up)`. Linking embedded modules
is embedding their composite (`link_embed`; the link's placeholder is
allocated and filled on one side only, never looked up), and an
environment for two-way modules is one for one-way modules
(`env_embed`). So a one-way security statement carries over
(`advantage_embed`), and with the ideal world linked: if `R` realises
`F ⊳ S` then `embed R` realises `embed F ∘ embed S` (`realises_embed`),
which is the form `uc_composition_link` takes. The case studies of
sections 4 to 6 plug in without change.

**Status.** Proved, no admits, for either mode: typing of `∘`
(`link_eq`, and `link_typed` in one direction), associativity,
environment extensions, the composition theorem, the embedding of
one-way modules and the bridge `realises_embed`. Not done: identities,
tensor and interchange for two-way modules; a first example with a back
edge (a bulletin board with an adversary `read` port).
