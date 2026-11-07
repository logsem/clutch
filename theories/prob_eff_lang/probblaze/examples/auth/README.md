# Authenticated channel from one-time MACs

`AUTH` realises the one-shot authenticated channel `F_AUTH` of the key
exchange over the raw network.  Both parties hold a preshared one-time
MAC key `(k₁, k₂)` per direction; a message `m` is sent as the pair
`(m, m^k₁ · g^k₂)`, and the receiver accepts the first pair whose tag
checks.  The raw network is the environment: it sees every pair and
decides what is delivered.  The simulator `S_AUTH` turns `F_AUTH`'s
leak-and-permit interface into the raw network's: it tags the leaked
message with its own key and permits delivery exactly when the
environment injects that pair.

The security of `AUTH` itself (the probability `2/q` of forging one of
the two tags) is a hypothesis here (`auth_realises`); the file proves what
follows from it by composition: DHKE run over `AUTH` instead of over
`F_AUTH`, with the bound `2/q` plus the DDH term.

| File | Contents |
|---|---|
| `auth_def.v` | The protocol `AUTH` and the simulator `S_AUTH`, as factories; the MAC `tag`. |
| `auth_typing.v` | The raw-network interface type `raw`, the typing of the MAC, and the typings of `AUTH` and `S_AUTH` at both modes. |
| `advantage_auth_dhke.v` | The composed systems `REAL_AUTH_DHKE = AUTH ∘f DH_KE`, `IDEAL_AUTH_DHKE`, `SIM_AUTH_DHKE = S_AUTH ∘f SIM_DHKE`, `RED_AUTH_DHKE`; the hypothesis `auth_realises`; the theorem `auth_dhke m` by `uc_composition_f`. |
