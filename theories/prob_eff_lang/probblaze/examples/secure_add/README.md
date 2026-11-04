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


## Three parties, one passively corrupted

Parties 0, 1 and 2 hold `x₀`, `x₁`, `x₂` and all learn `x₀ · x₁ · x₂`.
Each party `i` samples shares `r_p`, `r_q` for its two peers `p = i+1`,
`q = i+2` (mod 3), sends them, computes its sum
`s_i = x_i · (r_p · r_q)⁻¹ · b_p · b_q` from the shares `b_p`, `b_q` it
receives, sends `s_i` to both peers, and outputs `s_i · s_p · s_q`.

Party `c` is passively corrupted: it runs the protocol, but leaks its
samples and the messages it receives to the environment (IPDL style).  All
communication goes through one network functionality `F_NET`, which leaks
every header and lets the environment decide when a receive attempt
happens.  The environment acts as the scheduler: the scenario has type
`![MS] …`, so it can be called any number of times, each call being one
session, and the environment can set a session aside while a party waits
and start another one.  All functionalities therefore allocate their state
outside the session (`F_NET_gen`/`F_NET_sess`, `Π`/`Π_sess`,
`F_ADD3`/`F_ADD3_sess`).

The ideal functionality `F_ADD3` leaks `x_c`, and the output once all
inputs are in, to the simulator.  The simulator runs its own copy of the
protocol on its own network, with the dummy input 1 for the honest
parties.  It corrects the one message that would otherwise be
inconsistent with the output: the sum that `h = c+1` sends to `c` is
multiplied by `δ = y · x_c⁻¹`.  In the proof, the share that `h' = c+2`
sends to `h` is coupled with the simulator's by a shift of `x_{h'}⁻¹`, so
that every message `c` sees is identical in both worlds.  Both worlds run
the parties at the same point (in the handler of the port that starts
them), so the proof relates them step by step; the network, party and
typing layers are shared between the two directions.

| File | Contents |
|---|---|
| `add3_def.v` | Parties `party`/`run_party`, network `F_NET`, protocol `Π`, real world `R_ADD3 = F_NET ∘F Π`, functionality `F_ADD3`, simulator `S_ADD3` (with `patch` and `sim_leak`), ideal world `I_ADD3 = S_ADD3 ∘f F_ADD3`, semantic type `τ_ADD3`. |
| `add3_tbl.v` | The network's write-once mailbox tables, and specs for looking up a key. |
| `add3_net.v` | Relational spec of one network session, `F_NET_sess_spec`, generic in the two patches and in the relations on stored and delivered messages; client-side rules `brel_net_send`/`brel_net_recv`. |
| `add3_party.v` | Write-once ghost slots recording the real inputs and samples; the message relations `Rmsg`/`Rdeliv`; the group identities; one party's run in both worlds (`run_party_spec`, and the mirrored `run_party_spec_rev`). |
| `add3_prf.v` | The start invariant (which parties have run, `x_c`, `δ`), the simulator's patch (`patch_ok`), one session (`go_sess_spec`), the client's row and ports, and the refinement `R_ADD3_I_ADD3`. |
| `add3_prf_rev.v` | The mirrored argument and the refinement `I_ADD3_R_ADD3`. |
| `advantage_add3.v` | Syntactic type `T_ADD3` and the security theorem `adv_ADD3_typed`. |
| `scheduler_typed.v` | A syntactically typed generator-style scheduler that sets sessions aside, checking that the type system admits environments of this kind. |
