# Authenticated channel from one-time MACs

`AUTH` realises the one-shot authenticated channel `F_AUTH` of the key
exchange over the raw network.  Each direction has its own one-time MAC
instance, a pair of closures `(tag, verify)` over a key `(k₁, k₂)` that is
sampled at first use; a message `m` is sent as `(m, m^k₁ · g^k₂)`, and the
receiver accepts the first pair whose tag checks.  The raw network is the
environment: it sees every pair and decides what is delivered.  The
simulator `S_AUTH` turns `F_AUTH`'s leak-and-permit interface into the raw
network's: it tags the leaked message with an ideal MAC and permits delivery
exactly when the environment injects the tagged pair.

`adv_AUTH` bounds the advantage of a one-shot environment in telling `AUTH`
from `S_AUTH ∘f F_AUTH` by `2/q`, for a group of prime order `q`.  The
protocol is written over its MAC (`AUTH = AUTH_of MAC`) so that the proof
can swap the MAC:

1. `MAC ≈ MAC_pad`, exactly: when the tag comes first, it is a uniform
   group element (the exponent `k₂` is coupled with a pad), and `k₁` is only
   sampled when a different message is verified.
2. `MAC_pad ≈ MAC_ideal`, up to `1/q` per instance: they differ only when a
   pair that was not tagged verifies, which needs a freshly sampled exponent
   to hit one value.
3. `AUTH_of MAC_ideal ≈ S_AUTH ∘f F_AUTH`, exactly: both sessions have the
   handler skeleton of `F_AUTH`, and only the handler bodies are compared,
   under an invariant per message slot.

Step 2 spends error credits in every session, so the bound holds for
one-shot environments only.  `auth_dhke` composes it with the DHKE result:
DHKE run over `AUTH` instead of over `F_AUTH`, with the bound `2/q` plus the
DDH term.

| File | Contents |
|---|---|
| `auth_def.v` | The MAC instances `MAC`, `MAC_pad`, `MAC_ideal`; the session skeleton `auth_skel` and the bodies of the protocol, the simulator and `F_AUTH` (`F_AUTH_eq`); `AUTH_of`, `AUTH`, `S_AUTH`. |
| `auth_typing.v` | The interface types `MACT` and `raw`; typings of the MAC instances, of `AUTH_of M` for any typed `M`, and of `S_AUTH`. |
| `rand_avoid.v` | A coupling of two tapes along a bijection that avoids a list of values, paid by error credits. |
| `auth_mac.v` | Group facts (abelian, prime order); the relations `MAC ≈ MAC_pad` (exact) and `MAC_pad ≈ MAC_ideal` (`1/q`). |
| `auth_prf.v` | The skeleton lemma `auth_skel_rel`; the equivalence `AUTH_ideal ≈ S_AUTH ∘f F_AUTH` (`AUTH_SIM_EQ`, one proof in the logic of `eq/`) and its two directions. |
| `advantage_auth.v` | Lifting a MAC relation with credits to the protocol (`AUTH_of_err`); the theorem `adv_AUTH`. |
| `advantage_auth_dhke.v` | The composed systems `REAL_AUTH_DHKE = AUTH ∘f DH_KE`, `IDEAL_AUTH_DHKE`, `SIM_AUTH_DHKE = S_AUTH ∘f SIM_DHKE`, `RED_AUTH_DHKE`; the theorem `auth_dhke` by `uc_composition_f`. |
