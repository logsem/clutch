# Diffie–Hellman key exchange

Alice and Bob agree on a key `g^(ab)` over an authenticated channel: each
samples an exponent, sends its half `g^a` resp. `g^b` through `F_AUTH`, and
derives the key from the other's half.  The group is `valgroup`, written
multiplicatively; the environment sees the authenticated channel's leak
(the halves) and may query the key through the protocol's port.

The protocol `DH_KE` in the `F_AUTH`-hybrid world realises the ideal key
exchange `F_KE_lazy_alice` (which samples the key lazily, on the first
query) with the simulator `DH_SIM`, which fakes the halves.  The proof is
a reduction to decisional Diffie–Hellman: the real and ideal worlds are
each related to the protocol with its sampling replaced by a DDH oracle
(`C_lazy DH_real`, `C_lazy DH_rand`), and the two oracles are the DDH
games.  All systems are factories (`uc/DESIGN.md`); the statement is
mode-generic: at mode `MS` the bound is in terms of multi-instance DDH.

| File | Contents |
|---|---|
| `dhke_def.v` | The programs: `F_AUTH`, `DH_KE`, `DH_SIM`, `F_KE_lazy_alice`, the reduction `C_lazy` (a factory parametrised by a DDH oracle, with session `C_lazy_sess`) and its two instances `C_DH_real`, `C_DH_rand`; the DDH oracles `DH_real`, `DH_rand`; the systems `REAL_DHKE = F_AUTH ∘f DH_KE`, `IDEAL_DHKE = F_KE_lazy_alice`, `SIM_DHKE = F_AUTH ∘f DH_SIM`, `RED_DHKE`.  The eager functionality `F_KE` is kept for later use. |
| `dhke_common.v` | Ghost resources of the proofs (tokens, receipts, messages), the key-query theory `gk` and the authenticated-channel theories, the interface type `τ_DH` (equal to `τ__F aleak gk`). |
| `dhke_typing.v` | Interface types (`chan`, `aleak`, `gk`, `leakI`), the typings of the four systems at both modes, the typing of the reduction, the typing of `DH_KE`'s core, and the long-context typing tactics. |
| `dhke_eq.v` | Building blocks of the cores in the equivalence logic: `sample_or_read` in the protocol, the authenticated channel's send and receive rules (`eq_chan_send_bob`, …, `eq_chan_recv_alice`, …), the typing of the key query (`gk_typed`) and its theory (`gk_thy`). |
| `dhke_real.v` | The real world against the protocol with the real DDH oracle, one client call, as one equivalence `DH_KE_C_DH_real_EQ`; the refinements `DH_KE ≤ C_DH_real` and back are its instances. |
| `dhke_sim.v` | The simulated world against the protocol with the random oracle, one client call, as one equivalence `DH_SIM_F_KE_C_DH_rand_EQ`; the refinements `DH_SIM ∘f F_KE_lazy_alice ≤ C_DH_rand` and back are its instances. |
| `dhke_authchan.v` | `F_AUTH ≤ F_AUTH` with the message predicates of the surrounding proof, the lemma that threads the authenticated channel through the composites. |
| `advantage_dhke.v` | The typings of the composites and of the reduction environment, the four relations on the factories, `adv_DHKE m` (the bound against `DH_real`/`DH_rand`) and `dhke_realises m` (the same, with the simulator in the shape `SIM_DHKE ∘f IDEAL_DHKE` of the composition theorem).  The syntactic interface `T_DHKE` and the corollaries `adv_DHKE_typed`, `dhke_realises_typed` for syntactically typed environments. |
| `advantage_auth_dhke.v` | DHKE over the authenticated-channel protocol `AUTH` instead of `F_AUTH`: the composed systems `REAL_AUTH_DHKE = AUTH ∘f DH_KE`, `IDEAL_AUTH_DHKE`, `SIM_AUTH_DHKE = S_AUTH ∘f SIM_DHKE`, `RED_AUTH_DHKE`; the theorem `auth_dhke` by `uc_composition_f`. |
| `dhke_tapeless.v` | `DH_KE` against `DH_KE_tapeless`, which samples directly: both refinements, from the shared core typing `dh_core_typed` at the tape types `tape_l`/`tape_r` (a tape of one program, kept empty, against the unit of the other). |
| `dhke_closed_ctx.v` | `adv_DHKE_typed` for the multiplicative group of the RFC 3526 8192-bit prime at a concrete `gFunctors`; only the primality of that number is assumed. |

The compositions of DHKE with the secure channels are in
`secure_channel/`.
