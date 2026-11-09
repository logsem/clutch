# A logic for equivalences

Most relational results in the examples are equivalences, proved as two
refinements whose scripts mirror each other.  This directory defines a judgement

    EQ el ≈ er @ E <|X|> {{ R }}

over Iris's `monPred` with a two-point index `dirI = {Fwd, Bwd}`.  At `Fwd` it
is the refinement `BREL el ≤ er`; at `Bwd` it is `BREL er ≤ el`.  The program
`l` runs on the left at `Fwd` and on the right at `Bwd`, and `r` the other way
round.  State is described per program:

- `ℓ ↦ₗ v` and `ℓ ↦ᵣ v` are points-to assertions for `l` and `r`.
- `α ↪ₗN (N; ns)` and `α ↪ᵣN (N; ns)` are tapes for `l` and `r`.
- `⟪ τ ⟫ vl vr` lifts a semantic type to relate a value of `l` and a value of `r`.

A proof that uses only the rules here reads like a single directional proof.
`EQ_sem_typed` and `EQ_sem_typed_expr` turn it into the two typing judgements.

Label theories may depend on the direction (`eqThy`, a function from directions to
theories).  An ordinary theory, such as the theory of a semantic row, is coerced to a
constant one.  A theory created during a proof is built with `eq_thy_cons lls rls T X`:
`lls` and `rls` are the labels of `l` and `r`, and `T d` is the theory in direction
`d`.  Lifted types may depend on the direction too (`eq_lift_dep`), e.g. when a
polymorphic client is instantiated at a row built from the labels of one program.

`eq_rel` and `eq_lift` are sealed.  A proof that has to look at one direction
unfolds them with `eq_rel_at`, `eq_rel_at_elim` and `eq_lift_at`.

| File | Contents |
|---|---|
| `eq_logic.v` | The index, the judgement, the resources and lifted types.  Rules for values, pure steps given as a reduction sequence (`eq_rtc_pure_l`), non-atomic invariants, heap and tape steps, and couplings: tape/tape, tape/`rand`, `rand`/`rand`, along a bijection, and two tapes against one `rand`.  The lifting lemmas `eq_step_l`/`eq_step_r` (and the tactics `eq_lift_l`/`eq_lift_r`) turn a pair of refinement rules `brel_X_l`/`brel_X_r` into an `EQ` step.  `eq_brel_self` uses a symmetric refinement of a program with itself.  Tactics `eq_pures_l`, `eq_load_l`, …, `eq_focus_l`, and their `_r` versions. |
| `eq_valgroup.v` | Group operations of `valgroup` (`eq_exp_l`, `eq_mult_l`, `eq_eq_l`, …) and `eq_lift_group`. |
| `eq_finval.v` | Finite value types of `fin_val_type`: `eq_lift_fvt` and the tactics `eq_fvt_of_int_l Hx`, `eq_int_of_fvt_l fv` and their `_r` versions. |
| `eq_handlers.v` | Effects and handlers: fresh labels (`eq_effect_l`), new theories and labels (`eq_new_theory`, `eq_add_label_l`), `eq_learn_nodup`, `eq_thy_mono`, exhaustion (`eq_exhaustion`), performing an effect of a theory (`eq_introduction`), symmetric theories (`eq_thy_sym`, `eq_thy_app_sym`), distinctness of the labels of `l` (`eq_learn_labels_l`), one-shot handlers on one side (`eq_handle_os_l`) and on both sides (`eq_handle_os`, which gives the later that Löb induction over handled effects needs), continuations (`eq_cont_l`).  Tactics of the same names. |
| `eq_compat.v` | Rules from the semantic typing rules: `eq_call_frame`, a call through an effectful arrow type in evaluation contexts, keeping a frame; `eq_env_call`, a call to a typed operation of the environment from below a handler's theory. |

## Users

| Example | Equivalence |
|---|---|
| `examples/ske/ske.v` | `enc_real_tape_EQ` |
| `examples/prf/ske_prf.v` | `enc_real_red_real_EQ`, `red_ideal_hyb_EQ`, `hyb_ideal_EQ` |
| `examples/auth/auth_prf.v` | `AUTH_SIM_EQ` |
| `examples/secure_channel/advantage_ske_sec_chan.v` | reuses `enc_real_tape_EQ` |
| `examples/secure_add/secure_add_prf.v` | `ADD_EQ` |
| `examples/secure_channel/sec_channel_prf.v` | `SCHAN_EQ` |
| `examples/secure_channel/ske_sec_chan_prf.v` | `REAL_SKE_GAME1_EQ` |
| `examples/secure_channel/ske_sec_chan_ideal_prf.v` | `GAME2_IDEAL_SKE_EQ` |
| `examples/secure_add3/add3_prf.v` | `ADD3_EQ` (with `eq_run_party_c`/`_h` in `add3_party.v`) |
| `examples/dhke/dhke_real.v` | `DH_KE_C_DH_real_EQ` |
| `examples/dhke/dhke_sim.v` | `DH_SIM_F_KE_C_DH_rand_EQ` |

The two refinements keep their old names, as instances of the equivalence.

## Where proofs leave the abstraction

Rules in this directory are proved one direction at a time; that is their job.
Symmetric theories need no unfolding.  A theory is symmetric when swapping the
labels, the programs and the continuation relation leaves it unchanged;
`eq_thy_app_sym` then reads it at the `EQ` level as the ordinary theory, with
the labels of `l`.  The examples prove only the symmetry, as a plain Iris fact (`add_thy_sym`, `schan_thy_sym`,
`skechan_thy_sym`, `go_thy_sym`, `gk_thy_sym`).  Calls to typed operations of
the environment go through `eq_env_call`.

Outside this directory, a proof unfolds the judgement only in these places:

- **`auth_prf.v`, `eq_auth_skel`.**  The AUTH skeleton lemma `auth_skel_rel` is
  proved with the typing rules for handlers, which have no `EQ` counterpart.
  `eq_auth_skel` instantiates it in each direction with `sem_typed_inst3` and
  turns its refinement premises into `EQ` premises.
- **`ske.v`, `eq_rand_cipher_coupl`.**  The scheme's ciphertext coupling, lifted
  from its refinement version one direction at a time.
- **Three-party addition, the network (`add3_net.v`).**  The network's session spec
  `F_NET_sess_spec`, its client rules `brel_net_send`/`brel_net_recv` and the
  network invariant are proved for refinements and generic in the message
  relations.  `eq_F_NET_sess_spec`, `eq_net_send`, `eq_net_recv` and
  `eq_net_inv_alloc` instantiate them in each direction, with the relations
  flipped in direction `Bwd`; `eq_patch_spec_eq_at` turns the `EQ` spec of the simulator's patch
  into the per-direction one that `F_NET_sess_spec` expects.
- **Three-party addition, header operations (`add3_prf.v`).**  `F_NET_sess_spec`
  expects the environment's header operations as refinement-level specs
  (`env_op_spec`); `eq_hdr_spec_typed` provides them one direction at a time.
- **DHKE (`dhke_eq.v`, `dhke_real.v`, `dhke_sim.v`).**  The authenticated channel's rules
  (`eq_chan_send_bob`, `eq_chan_send_alice`, `eq_chan_recv_alice`,
  `eq_chan_recv_bob`) are proved one direction at a time.  The refinements that the composition in
  `advantage_dhke.v` consumes (`DH_KE_C_DH_real`, `C_DH_real_DH_KE`,
  `DH_SIM_F_KE_C_DH_rand`, `C_DH_rand_DH_SIM_F_KE`) are the two equivalences
  read in each direction; its postcondition nests
  relations, so `EQ_sem_typed` does not apply.

## Not yet covered

The remaining mirrored proofs: OT.  It needs couplings with avoid lists paid by error credits, which have no `EQ` rules yet.
