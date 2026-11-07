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
| `dhke_common.v` | Ghost resources of the proofs (tokens, receipts, messages), the key-query theory `gk` and the authenticated-channel theories, the interface types `τ_DH`/`τ_DH_OS`. |
| `dhke_typing.v` | Interface types (`chan`, `aleak`, `gk`, `leakI`), the typings of the four systems at both modes, the typing of the reduction, the typing of `DH_KE`'s core, and the long-context typing tactics. |
| `dhke_real_one.v`, `dhke_real_other.v` | The real world against the protocol with the real DDH oracle: `DH_KE ≤ C_DH_real` and back, one client call. |
| `dhke_sim_one.v`, `dhke_sim_other.v` | The simulated world against the protocol with the random oracle: `DH_SIM ∘f F_KE_lazy_alice ≤ C_DH_rand` and back. |
| `dhke_authchan.v` | `F_AUTH ≤ F_AUTH` with the message predicates of the surrounding proof, the lemma that threads the authenticated channel through the composites. |
| `advantage_dhke.v` | The typings of the composites and of the reduction environment, the four relations on the factories, `adv_DHKE m` (the bound against `DH_real`/`DH_rand`) and `dhke_realises m` (the same, with the simulator in the shape `SIM_DHKE ∘f IDEAL_DHKE` of the composition theorem). |

The compositions of DHKE with the secure channels are in
`secure_channel/`, the one with the authenticated-channel protocol in
`auth/`.
