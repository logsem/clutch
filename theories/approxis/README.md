# PR for Internship Summer of 2025

Apart from stream & DH assumptions, the other files modified or added are in the folder theories/approxis.

## In theories/clutch: Stream & DH assumptions
Files: `stream.v` and `DH_assumptions.v`

- `stream.v` proves equivalence of two streams of random integers under a bijection between the range of randoms;
- `DH_assumptions.v` proves reduction of discrete logarithm, computational Diffie-Hellmann and decisional Diffie-Hellmann problems.

## Asymmetric scheme
File: `pubkey_class.v`

Same as `pubkey.v` but in a typeclass.

## Initializable Symmetric Encryption Scheme
File: `symmetric_init.v`

To encompass the idealized random function-based encryption scheme, and other scheme that rely on initialization and mutable state, possibly shared between encryption and decryption, this class extends symmetric.v.

The class `SYM_init` has a field `enc_scheme : expr` instead of the two vals `enc` and `dec`. This expression can initialize some states (for instance, the map of the random function).

## Iterable Expression
File: `iterable_expression.v`

This file attemps to formalize several properties on expression:
- determinism: this is quite usable, this is for instance used in `valgroup.v` to describe `vg_of_int` and `int_of_vg`.
- iterable: the idea is that we can run once the program on the LHS (resp. RHS) of the refinement, and re-produce the same value when running the same code on the RHS (resp. LHS). This one is less useable.
- package: attempt at formalizing a package, not practical and really hard to manipulate.

## Clutch Group
Files: `valgroup.v`, `valgroupZp.v` and `valgroupZpx.v`

Several changes occured in clutch group definitions, all were needed to prove the kemdem example.

The `vg_of_int` and `int_of_vg` functions are assumed to be deterministic, as described in the iterable expression file.
The semantic counterpart of `int_of_vg` is assumed to be the inverse of the semantic `vg_of_int`.
`vgval` is assumed to be semantically typed.

All these properties were proved for the two instances available, so `valgroupZp` and `valgroupZpx` remain valid instances of a clutch group.

## PRG/PRF
Files: `prg_extension.v` and `prg_prf.v`

We prove two important properties of the PRGs:
- In `prg_extension.v`, we prove the extension property, namely that from a PRG adding d random bits to a random generator, we can construct another PRG adding 2*d random bits. This proof was one of the first one I wrote, so it is actually not valid: it does not reduce to the PRG game, but assume an erroneous lemma allowing to permute the left/right side of the game in-proof, greatly simplifying the reasoning. It should be redone properly.
- In `prg_prf.v`, we prove we can construct a PRF if we have a PRG. This proof is not complete, however, we need some assumptions on the PRG, namely that it is iterable, to carry out the proof.

The extension proof comes from section 5.4 of The Joy of Cryptography, Mike Rosulek, 2020.
The construction of a PRF is Construction 5.4 of The Joy of Cryptography, Mike Rosulek, 2020.

## One-Time Pad (OTP)
File: `one_time_pad.v`

We add a symmetric encryption scheme satisfying one-time secrecy and prove it satisfies one-time CPA.

The adequacy theorem is not applied at the end.

A description of the scheme can be found in Construction 1.1 of The Joy of Cryptography, Mike Rosulek, 2020.

## KEMDEM
Files: `kemdem_hybrid_cpa_generic.v`, `kemdem_hybrid_cpa_instance_otp.v` and `kemdem_hybrid_cpa_instance_rf.v`

We prove CPA security of a KEMDEM scheme, based on:
- an opaque symmetric scheme satisfying one-time CPA security;
- an opaque asymmetric scheme satisfying CPA security.

The hypotheses needed to instantiate this security property take the form of several typeclass.

The adequacy theorem is not applied at the end.

Reference: [https://garbledcircus.com/kemdem/left-right](https://garbledcircus.com/kemdem/left-right)

### ElGamal + RF-based encryption instance

We instantiate 

`vg_of_symkey`: rejection sampler
Some assumptions about `vg_of_int` are missing. The `vg_of_symkey` function spec is admitted.

Admitted because of problems with group operations.

### ElGamal + OTP instance

Assumption as hypothesis over `vg_of_int` to have a proper map from OTP keys to ElGamal messages.

Admitted because of problems with group operations.

## Integrity assumptions
Files: `symmetric_init.v`, `intptxt_ideal_dec.v` and `intctxt_ideal_dec.v`

We add integrity of plaintexts (INT-PTXT) definition in `symmetric_init.v` and showed that it's equivalent to replacing decryption by an ideal one in `intptxt_ideal_dec.v`, that can be more useful in proofs.

The goal would be to do the same proof for integrity of ciphertexts (INT-CTXT), the idealized decryption is already defined in `intctxt_ideal_dec.v`. This proof would require to have more general map lemmas (`refines_get_l`, etc).

## Wide-Mouthed Frog (WMF) protocol
Files: `wmf_protocol.v`, `wmf_attack.v`, `wmf_active_attacker_security.v` and `wmf_eav_security`.

## Definitions

We define several variants of the protocol in `wmf_protocol.v`, informally described below:
```
A -> S : (A, {B, N}_ka)
S -> B : {A, N}_kb
```
where:
- A and B are agent, exchanging a secret nonce `N`;
- S is a server trusted by both parties, having access to symmetric keys to communicate with both agents.

References: [https://lsv.ens-paris-saclay.fr/Software/spore/wideMouthedFrog.html](https://lsv.ens-paris-saclay.fr/Software/spore/wideMouthedFrog.html)

## Eeavesdropping attacker

We prove the security of the protocol against an eavesdropping attacker, assuming the symmetric encryption satisfies the IND-CPA$ game.

The model simply computes each message and gives them in order, and to the destinators intended, and provide the trace of all messages that appeared on the network to the attacker.

The adequacy theorem is not applied at the end.

## Active attacker

This proof could not be carried out until the end.
To finish it, we must define the CTXT game, and prove under this assumption we can replace decryption by looking up an associative map recording ciphers and plaintexts encrypted by the encryption oracle. For more details, see `intctxt_ideal_dec.v`.

## Attack

We weaken the protocol to obtain an unsafe one, and model an on-path attack on this protocol.

In this version of the protocol, we simply encrypt only the nonce and not the destinator's tag in the first message:
```
A -> S : (A, B, {N}_ka)
S -> B : {A, N}_kb
```

The attack works as follows, assuming there is a dishonest agent with tag `Bd`:
- `A` sends to `S` the message `(A, B, {N}_ka)`, where `N` is a honest nonce;
- the attacker intercepts this message, replace the destinator's tag by a dishonest tag, thus sending the message `(A, Bd, {N}_ka)` to `S`;
- the server can decrypt the nonce, and sends `{A, N}_kbd` to `Bd`, where `kbd` is a symmetric key shared between `S` and `Bd`;
- `Bd` (or the attacker) can decrypt the nonce `N`.
