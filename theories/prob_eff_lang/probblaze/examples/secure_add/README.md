# Secure addition

Alice holds `x`, Bob holds `y`, and Charlie (the aggregator) learns
`x · y` and nothing else.  The group is written multiplicatively, as in
`valgroup`.

1. Alice samples a mask `r`, sends `r` to Bob and `x · r` to Charlie.
2. Bob, once he has received `r`, sends `y · r^-1` to Charlie.
3. Charlie outputs `(x · r) · (y · r^-1) = x · y`.

Alice's mask travels over a one-shot secure channel `F_CHAN`
(`DH_KE/sec_channel_def.v`).  Each scenario below is proved perfectly
secure: no well-typed environment can distinguish the real protocol from
the ideal functionality composed with a simulator, so the advantage is 0.

## Corrupt Charlie

Charlie and the network are the environment: Alice and Bob send their
messages to Charlie through environment operations, and only the A-to-B
channel is an `F_CHAN`.  The simulator samples Charlie's view of Alice's
message and completes Bob's message from the output.

| File | Contents |
|---|---|
| `add_corrupt_C_def.v` | Protocol `π_ADD`, real world `R_ADD = F_CHAN ∘F π_ADD`, functionality `F_ADD`, simulator `S_ADD`, ideal world `I_ADD = S_ADD ∘f F_ADD`, semantic type `τ_ADD`. |
| `add_corrupt_C_bijection.v` | The coupling `add_coupling_nat` of Alice's mask with the simulator's sample, and the group facts `vgG_comm` and `add_mask_cancel`. |
| `add_corrupt_C_prf.v` | Both directions of the equivalence, `R_ADD_I_ADD` and `I_ADD_R_ADD`, and the helper `brel_env_call` for calling environment operations from inside a handler. |
| `advantage_add_corrupt_C.v` | Syntactic type `T_ADD` and the security theorem `adv_ADD_typed`. |

## No corruption

Charlie is an honest party with an output port, and all three messages go
over `F_CHAN`s (A to B, A to C, B to C).  The environment is the network: it
sees the six channel leaks and decides on delivery.  The masks never reach
the environment, so no coupling is needed.

| File | Contents |
|---|---|
| `add_honest_def.v` | Protocol `π_ADD3`, real world `R_ADD3` (three `F_CHAN`s around `π_ADD3`), functionality `F_ADD3`, simulator `S_ADD3`, ideal world `I_ADD3 = S_ADD3 ∘f F_ADD3`, semantic type `τ_ADD3`. |
| `add_honest_prf.v` | Both directions of the equivalence, `R_ADD3_I_ADD3` and `I_ADD3_R_ADD3`, with one-sided sampling rules `brel_rand_l/r`. Reuses `brel_env_call` and `vgG_comm` from the corrupt-Charlie files. |
| `advantage_add_honest.v` | Syntactic type `T_ADD3` and the security theorem `adv_ADD3_typed`. |

## Notes

`SKETCHES.md` has design notes for these developments and sketches of
further case studies: corrupt Alice or Bob, the classic three-party sum,
coin flipping, and multiplication with Beaver triples.
