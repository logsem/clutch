# Oblivious transfer

A 1-out-of-2 oblivious transfer in the common-reference-string model
(`F_CRS`), with a corrupt receiver and with a corrupt sender.  With a
corrupt receiver the real protocol is statistically close to the ideal
functionality with its simulator (`adv_ot_rc`: bound `3/n` for a group of
order `n`); with a corrupt sender the bound is a DDH term plus `2/n`
(`adv_ot_final`, through the reduction `OT_REDUCTION`).  Both also come
in versions for syntactically typed environments.

This case study predates the factory presentation of `uc/DESIGN.md`: its
systems are closures that allocate their state when they take the
client, and the top-level statements are on those closures rather than on
factories of a mode.

| File | Contents |
|---|---|
| `ot_common.v` | Ghost resources and effect theories shared by both corruption cases. |
| `ot_bijection.v` | The couplings on the group used by the simulators. |
| `definition_thunk_receiver_corrupt.v`, `OT_Rcorrupt_thunk.v` | The protocol, functionality and simulator with a corrupt receiver, and the two relations. |
| `definition_thunk_sender_corrupt.v`, `OT_SCorrupt_thunk.v` | The same with a corrupt sender. |
| `advantage_ot.v` | The security theorems for both cases. |
| `definitions.v`, `definition_os.v`, `definition_mut.v`, `definition_mut_sender_corrupt.v`, `OT_Scorrupt_mut.v` | Earlier formulations (labelled, one-shot and multi-shot variants); `OT_Scorrupt_mut.v` is admitted. |
