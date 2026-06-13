(** Scratch / experimental specs around the Sparse Vector Technique, ported from
    [clutch.diffpriv.examples.SVT_experiments] to the GENERIC language.

    IMPORTANT: in the original development EVERY lemma in this file is [Abort]ed
    (and [AT_NF_safe]-style helpers were [Admitted]); the file collects failed or
    speculative proof attempts (it even contains [Fail …]/[give_up]/[admit] mid
    script).  None of these are real verified artifacts.  We therefore port the
    genuine content — the experimental DEFINITIONS [WP_PWEQ] / [magic_post] and the
    lemma STATEMENTS — and leave the (scratch, non-replaying) proof scripts
    [Abort]ed exactly as upstream, rather than porting tactic-by-tactic dead code.

    Signature setup and the [diffprivGS Ssvt Σ] context are inherited from
    [sparse_vector_technique] (imported below). *)
From iris.base_logic Require Export na_invariants.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_choice.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_diffpriv.examples Require Import list sparse_vector_technique.
From iris.prelude Require Import options.

#[global] Opaque sample_idx.

Section svt_experiments.
  Context `{!diffprivGS Ssvt Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Ssvt)).

  #[local] Open Scope R.

  (* The first spec with equal return values in the postcondition.  In the
     original this was only "concluded" by assuming dubious rules; left [Abort]ed. *)
  Lemma above_threshold_online_spec (num den T : Z) (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯m (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold_reset) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold_reset) #num #den #T (Val (inject db))
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               AUTH ∗
               (∀ q, wp_sensitive Ssvt (Val q) 1 dDB dZ -∗
                     AUTH -∗
                     ⤇ fill K (f' q) -∗
                     WP (Val f) (Val q)
                       {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                   ⌜ v = v' ⌝ ∗
                                   (⌜ v = SOMEV #false⌝ -∗ AUTH)
                       }}
               )
       }}.
  Proof.
    (* scratch / dubious-rule-dependent in the original development *)
  Abort.

  (* Question: If we had a WP rule for pointwise equality, could we use it to strengthen the
     pointwise AT spec into the exact one?  Speculative; the postcondition's [⌜RES = false⌝ -∗ AUTH]
     also mentions the variable that the pointwise equality quantifies over. *)
  Definition WP_PWEQ : iProp Σ :=
    ∀ (e e' : expr) K,
      (∀ RES : val, ⤇ fill K e' -∗
                    WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = RES -> v' = RES⌝}})
      -∗
      (⤇ fill K e' -∗ WP e {{ v, ⤇ fill K (of_val v) }}).

  Lemma pweq_frame_nodep e e' K : WP_PWEQ -∗ ∀ (AUTH : iProp Σ),
      (∀ RES : val,
          ⤇ fill K e' -∗
          WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = RES -> v' = RES⌝ ∗ AUTH }}) ∗
      ⤇ fill K e' -∗
        WP e
          {{ v, ⤇ fill K (Val v) ∗
                AUTH
               }}.
  Proof.
    (* scratch; ends in [give_up] in the original development *)
  Abort.

  Definition magic_post :=
    forall e Φ Ψ Ξ R,
    (R -∗ WP e {{ v , Φ v ∗ Ξ v }}) ∗
    ((R -∗ WP e {{ v , Φ v }}) -∗ R -∗ WP e {{ v , Ψ v}}) ⊢ R -∗ WP e {{ v , Ψ v ∗ Ξ v }}.

  Lemma pweq_frame e e' K : WP_PWEQ -∗ ∀ (AUTH : val -> iProp Σ),
      (∀ RES : val,
          ⤇ fill K e' -∗
          WP e {{ v, ∃ v', ⤇ fill K (of_val v') ∗ ⌜v = RES -> v' = RES⌝ ∗ AUTH RES }}) ∗
      ⤇ fill K e' -∗
        WP e
          {{ v, ⤇ fill K (Val v) ∗
                AUTH v
               }}.
  Proof.
    (* scratch / open in the original development *)
  Abort.

  Lemma above_threshold_online_no_flag_spec_pw_no_AUTH (num den T : Z) (εpos : 0 < IZR num / IZR den) K :
    ↯m (IZR num / (2 * IZR den)) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T)
    -∗
    WP (Val above_threshold) #num #den #T
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
               ( ∀ `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1)
                   q, wp_sensitive Ssvt (Val q) 1 dDB dZ -∗
                      ⤇ fill K (f' (Val (inject db')) q) -∗
                      ∀ R : bool, (if R then ↯m (IZR num / (2 * IZR den)) else emp) -∗
                        WP (Val f) (Val (inject db)) (Val q)
                          {{ v, ∃ v', ⤇ fill K (Val v') ∗
                                      ⌜ v = v' ⌝
               }} )
       }}.
  Proof.
    (* The below-threshold case is not provable from the available assumptions
       (the original ends this branch in [give_up]); left [Abort]ed. *)
  Abort.

End svt_experiments.
