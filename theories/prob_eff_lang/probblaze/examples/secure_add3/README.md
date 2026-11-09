# Three-party secure addition, one party passively corrupted

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
and start another one.  All functionalities are factories (`uc/DESIGN.md`) that
allocate one instance when called; the sessions of that instance are the
environment's calls (`F_NET`/`F_NET_sess`, `Π`/`Π_sess`, `F_ADD3`/`F_ADD3_sess`).
This is the multi-session example of the development.

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
| `add3_def.v` | Parties `party`/`run_party`, network `F_NET`, protocol `Π`, the real system `REAL_ADD3 c = F_NET ∘F Π c`, functionality `F_ADD3` (`IDEAL_ADD3`), simulator `S_ADD3` (`SIM_ADD3`, with `patch` and `sim_leak`), semantic type `τ_ADD3`. |
| `add3_tbl.v` | The network's write-once mailbox tables, and specs for looking up a key. |
| `add3_net.v` | Relational spec of one network session, `F_NET_sess_spec`, generic in the two patches and in the relations on stored and delivered messages; client-side rules `brel_net_send`/`brel_net_recv`.  Their versions for the equivalence logic: `eq_F_NET_sess_spec`, `eq_net_send`, `eq_net_recv`. |
| `add3_party.v` | Write-once ghost slots recording the real inputs and samples; the message relations `Rmsg`/`Rdeliv`; the group identities; one party's run in both worlds, as an equivalence (`run_party_spec`, `eq_run_party_c`, `eq_run_party_h`). |
| `add3_prf.v` | The start invariant (which parties have run, `x_c`, `δ`), the simulator's patch (`eq_patch_ok`), one session (`eq_go_sess_spec`), the client's row and ports, and the equivalence `ADD3_EQ`, with the refinements `REAL_ADD3_IDEAL_MS` and `IDEAL_REAL_ADD3_MS` as instances. |
| `advantage_add3.v` | The security theorem `adv_ADD3 m` for environments `A : fac m τ_ADD3 → 𝔹`, and `adv_ADD3_typed` for syntactically typed environments (`T_ADD3`). |
| `scheduler_typed.v` | A syntactically typed generator-style scheduler that sets sessions aside, checking that the type system admits environments of this kind. |
