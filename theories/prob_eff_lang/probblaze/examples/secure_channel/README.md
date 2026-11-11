# One-message secure channels

Alice sends one message to Bob confidentially, using a key from the key
exchange and an authenticated channel: the protocol `CHAN` asks the key
exchange for the key, hides the message with it, and sends the result
over the one-shot authenticated channel `F_OAUTH`.  The environment sees
`F_OAUTH`'s leak (the ciphertext) and the key exchange's leak, and decides
on delivery.  The ideal functionality `F_CHAN` leaks only that a message
was sent and lets the environment decide on delivery; the simulator
replaces the ciphertext by a fresh random one.

Two variants of the scheme, in parallel developments:

* **mask**: the message is a group element and is hidden by a group
  operation with the key (`mask.v`, the class `Mask`); the real and ideal
  worlds are perfectly indistinguishable (`adv_SCHAN m ≤ 0`).
* **SKE**: the message is encrypted with an abstract symmetric scheme
  (`ske/ske.v`, the class `SYM`); the bound is the advantage against the
  scheme's real/ideal encryption oracles (`adv_SKE m`), which `prf/`
  instantiates with a PRF-based scheme.

Both are then composed with DHKE through the composition theorem
(`uc/uc_theorem.v`): the key exchange in the hybrid world is `REAL_DHKE`,
the composed simulator is `SIM_DHKE` plugged into the channel simulator.
All systems are factories and all statements are mode-generic
(`uc/DESIGN.md`).

| File | Contents |
|---|---|
| `mask.v`, `mask_bijection.v` | The masking operation as a class (`Mask`, `Mask_struc`) and the coupling of a masked message with a uniformly random one. |
| `sec_channel_def.v` | Mask variant: `F_OAUTH`, `CHAN`, `F_CHAN`, `CHAN_SIM_lazy`; the systems `REAL_SCHAN = (F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN`, `IDEAL_SCHAN`, `SIM_SCHAN`. |
| `sec_channel_typing.v` | Mask variant: interface types (`oaleak`, `cli`, `hdl`) and the typings of `F_OAUTH` and `CHAN`. |
| `sec_channel_ideal_typing.v` | Mask variant: the leak type `fleak` and the typings of `F_CHAN` and `CHAN_SIM_lazy`. |
| `sec_channel_prf.v` | Mask variant: the effect theories of the channel and the two relations `R_CHAN_SIM_f`/`SIM_R_CHAN_f` between the real and the simulated world. |
| `advantage_sec_channel.v` | Mask variant: `adv_SCHAN m` (perfect).  `adv_SCHAN_typed` for syntactically typed environments (interface `T_SCHAN`). |
| `advantage_dhke_sec_channel.v` | DHKE + mask channel: `REAL_DHKE_CHAN`, `IDEAL_DHKE_CHAN`, `SIM_DHKE_CHAN`, `RED_DHKE_CHAN` and `dhke_chan_realises m` by `uc_composition`.  `dhke_chan_realises_typed` for syntactically typed environments (`T_DHKE_CHAN`). |
| `ske_sec_chan_def.v` | SKE variant: `F_OAUTH`, `CHAN`, `F_CHAN`, `CHAN_SIM`, the reduction `RED_CHAN` (a factory parametrised by an encryption oracle, with session `RED_CHAN_sess`), the hybrids `GAME1`/`GAME2`, the systems `REAL_SKE`, `IDEAL_SKE`, `SIM_SKE`, `RED_SKE`. |
| `ske_sec_chan_common.v` | SKE variant: effect theories of the channel, the key-coupling bijection, tape lemmas, the interface type `τsc`. |
| `ske_sec_chan_typing.v` | SKE variant: interface types and the typings of `F_OAUTH`, `CHAN`, the reduction and the encryption oracles. |
| `ske_sec_chan_prf.v`, `ske_sec_chan_ideal_prf.v` | SKE variant: the four relations `REAL_SKE ≃ GAME1` and `GAME2 ≃ SIM_SKE ∘f IDEAL_SKE`. |
| `advantage_ske_sec_chan.v` | SKE variant: the typings of the composites and of the reduction environment, the taped/untaped oracle relation, `adv_SKE m` (the bound against `enc_real`/`enc_ideal`).  `adv_SKE_typed` for syntactically typed environments (`T_SKE`). |
| `advantage_dhke_ske_sec_chan.v` | DHKE + SKE channel: the typings of the SKE ideal side (`F_CHAN`, `CHAN_SIM`), the composed systems `REAL_DHKE_SKE`, `IDEAL_DHKE_SKE`, `SIM_DHKE_SKE`, the two reductions, and `dhke_ske_realises m` by `uc_composition`.  `dhke_ske_realises_typed` for syntactically typed environments (`T_DHKE_SKE`). |
| `xor.v` | An XOR mask over bit strings (unused by the current results). |
