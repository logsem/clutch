# Secure addition with a corrupt aggregator

Alice holds `x`, Bob holds `y`, and Charlie (the aggregator) learns
`x · y` and nothing else.  The group is written multiplicatively, as in
`valgroup`.

1. Alice samples a mask `r`, sends `r` to Bob and `x · r` to Charlie.
2. Bob, once he has received `r`, sends `y · r^-1` to Charlie.
3. Charlie outputs `(x · r) · (y · r^-1) = x · y`.

Alice's mask travels over a one-shot secure channel `F_CHAN`
(`secure_channel/sec_channel_def.v`).  Charlie and the network are the
environment: Alice and Bob send their messages to Charlie through
environment operations, and only the A-to-B channel is an `F_CHAN`.  The
simulator samples Charlie's view of Alice's message and completes Bob's
message from the output.

All systems are factories (`uc/DESIGN.md`): `π_ADD`, `F_ADD` and `S_ADD`
allocate their state when called and then take the client.  The scenario
is perfectly secure: no well-typed environment can distinguish the real
protocol from the ideal functionality composed with the simulator, at
either mode.

| File | Contents |
|---|---|
| `secure_add_def.v` | Protocol `π_ADD`, functionality `F_ADD`, simulator `S_ADD`, the systems `REAL_ADD = F_CHAN ∘F π_ADD`, `IDEAL_ADD = F_ADD`, `SIM_ADD = S_ADD`, and the semantic type `τ_ADD`. |
| `secure_add_bijection.v` | The coupling `add_coupling_nat` of Alice's mask with the simulator's sample, and the group facts `vgG_comm` and `add_mask_cancel`. |
| `secure_add_prf.v` | Both directions of the equivalence on the factories, `REAL_ADD_IDEAL_MS` and `IDEAL_REAL_ADD_MS`, and the helper `brel_env_call` for calling environment operations from inside a handler. |
| `advantage_secure_add.v` | The security theorem `adv_ADD m` for environments `A : fac m τ_ADD → 𝔹`, and `adv_ADD_typed` for syntactically typed environments (`T_ADD`). |

The three-party protocol with a passively corrupted party is in
`secure_add3/`.
