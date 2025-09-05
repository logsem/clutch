# RClutch Progress Sept 2025

Status: 
- `Ok` Completely finished
- `Opt` Lemmas that are not required for mvp 
- `Adm` Admit that is probably true
- `Idk` Admit that I don't know if it's true
- `Punishment` Blocked by Rocq issues that I have not figured out how to resolve (import order, canonical structures, notation clashing, etc)
- `Unported` Statements are still not ported

## `prob/monad`

| Name                 | Status                  |
|----------------------|-------------------------|
| ``couplings_app.v `` | `Opt`                   |
| ``giry.v          `` | Several `Adm` and `Idk` |
| ``lim.v           `` | `Ok`                    |
| ``meas_markov.v   `` | `Opt`                   |
| ``prelude.v       `` | 2 `Adm`                 |
| ``preprelude.v    `` | `Ok`                    |
| ``tactics.v       `` | `Ok`                    |

## `meas_lang/lang`

| Name                | Status                  |
|---------------------|-------------------------|
| ``cfg.v ``          | `Ok`                    |
| ``constructors.v `` | `Ok`                    |
| ``cover.v ``        | `Ok`                    |
| ``fill.v``          | `Opt` (2x slow proofs)  |
| ``heapops.v ``      | `Ok`                    |
| ``lang.v``          | 1 `Adm`, 1 `Opt` (slow) |
| ``prelude.v``       | `Ok`                    |
| ``projections.v``   | `Ok`                    |
| ``pureops.v``       | `Ok`                    |
| ``randops.v``       | `Ok`                    |
| ``shapes.v``        | `Ok`                    |
| ``state.v``         | `Ok`                    |
| ``subst.v``         | `Ok`                    |
| ``tapes.v``         | `Ok`                    |
| ``types.v``         | `Ok`                    |
    
## `meas_lang/spec`

| Name                | Status      | Notes                                                                                 |
|---------------------|-------------|---------------------------------------------------------------------------------------|
| ``spec_ra.v ``      | `Ok`        |                                                                                       |
| ``spec_rules.v ``   | `Unported`, | Blocked on notation, not convinced my solution to canonical structures issue is right |
| ``spec_tactics.v `` | `Unported`  | Ask Simon about `gwp` eventually                                                      |

## `meas_lang/typing`

| Name                         | Status |
|------------------------------|--------|
| ``contextual_refinement.v `` | `Ok`   |
| ``types.v ``                 | `Ok`   |


## `meas_lang`

| Name                   | Status       | Notes                                                                     |
|------------------------|--------------|---------------------------------------------------------------------------|
| ``class_instances.v `` | A few `Adm`  | Some lemmas need to be stated                                             |
| ``ctx_subst.v``        | `Unported`   | Why does this exist?                                                      |
| ``ectxi_language.v``   | `Ok`         |                                                                           |
| ``ectx_language.v``    | 3 `Adm`      |                                                                           |
| ``erasable.v``         | `Unported`   |                                                                           |
| ``erasure.v``          | `Punishment` | Likely similar to the problem with `spec_rules`, proofs statued but stuck |
| ``exec.v``             | `Unported`   | Why does this exist?                                                      |
| ``exec_lang.v``        | `Unported`   | Why does this exist?                                                      |
| ``language.v``         | `Ok`         |                                                                           |
| ``meas_spec_update.v`` | `Ok`         |                                                                           |
| ``metatheory.v``       | `Unported`   |                                                                           |
| ``notation.v``         | `Opt`        |                                                                           |
| ``tactics.v``          | `Adm`        | Need `solve_red`                                                          |
| ``wp_tactics.v``       | `Unported`   | Ask Simon about `gwp` eventually                                          |


## `micrometer`

| Name                 | Status               | Notes                            |
|----------------------|----------------------|----------------------------------|
| ``adequacy.v ``      | 2 `Adm`              |                                  |
| ``adequacy_rel.v ``  | `Unported`           |                                  |
| ``app_rel_rules.v `` | `Unported`           |                                  |
| ``app_weakestpre.v`` | Several `Adm`, `Idk` |                                  |
| ``compatibility.v``  | `Unported`           |                                  |
| ``coupling_rules.v`` | `Unported`           |                                  |
| ``derived_laws.v``   | `Unported`           |                                  |
| ``ectx_lifting.v``   | 1 `Adm`              |                                  |
| ``fundamental.v``    | `Unported`           |                                  |
| ``interp.v``         | `Unported`           |                                  |
| ``lifting.v``        | `Ok`                 |                                  |
| ``micrometer.v``     | `Ok`                 |                                  |
| ``model.v``          | `Unported`           |                                  |
| ``primitive_laws.v`` | Many `Idk`           |                                  |
| ``proofmode.v``      | `Unported`           | Ask Simon about `gwp` eventually |
| ``rel_tactics.v``    | `Unported`           |                                  |
| ``soundness.v``      | `Unported`           |                                  |
