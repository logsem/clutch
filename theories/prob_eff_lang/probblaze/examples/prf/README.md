# Encryption from a pseudorandom function

A symmetric encryption scheme built from an abstract keyed function
`prf : key → nonce → message`: `enc k m = (r, prf k r + m)` for a fresh
nonce `r` (`PRF_SKE`), with the ciphertext space the product of nonces and
messages.  The scheme's real/ideal encryption oracles are reduced to the
PRF games `prf_real`/`prf_ideal` through the reduction `red_prf`
(`adv_enc_prf`).  This instantiates the SKE secure channel of
`secure_channel/` and its composition with DHKE, giving bounds against the
PRF games.  The PRF assumption is available for one-shot oracles, so the
front-end theorems are stated for single-session environments (`fac OS`).

| File | Contents |
|---|---|
| `ske_prf.v` | The classes `PRF_struct`/`PRF`, the games `prf_real`/`prf_ideal`, the scheme `PRF_SKE` as an instance of `SYM`, the reduction `red_prf` and the bound `adv_enc_prf`. |
| `prf_results.v` | `adv_schan_prf` (the SKE channel with the PRF-based scheme, against the PRF games) and `adv_composition_prf` (DHKE followed by that channel: a DDH term plus a PRF term). |

The abstract scheme (`SYM`, the oracles `enc_real`, `enc_real_tape`,
`enc_ideal`) is in `ske/ske.v`.
