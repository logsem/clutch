From clutch.diffpriv_simple Require Import diffpriv_simple.

Section pweq.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Definition WP_PWEQ := ∀ e e' K E,
    (
      ∀ (RES : val),
      ⤇ fill K e' -∗
          WP e @ E
            {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }} )
-∗
    (⤇ fill K e'
    -∗
     WP e @ E
      {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = v'⌝ }}).

  Lemma wp_pweq : WP_PWEQ.
  Proof.
    iLöb as "IH".
    iIntros (e e' K E) "pw rhs".
    rewrite wp_unfold /wp_pre.
    destruct (language.to_val e) eqn:He.
    { iSpecialize ("pw" $! v).
      rewrite wp_unfold /wp_pre //= He.
      iMod ("pw" with "rhs") as "pw". iModIntro. iDestruct "pw" as "(%v' & v' & %pweq)".
      iExists v'. iFrame. rewrite pweq => //.
    }
    iIntros (?????) "(StI & SpI & ErI)". iSimpl in "IH".
    iAssert (|={E,∅}=> ⌜reducible (e, σ1)⌝ ∗
    ∃ (R2 : language.cfg prob_lang → language.cfg prob_lang → Prop)
      (ε1 ε2 δ1 δ2 : nonnegreal) (n : nat),
      ⌜DPcoupl (prim_step e σ1) (pexec n (e1', σ1')) R2 ε1 δ1⌝ ∗
      ⌜ε1 + ε2 <= ε⌝ ∗ ⌜δ1 + δ2 <= δ⌝ ∗
      ∀ e2 σ2 e2' σ2',
        ⌜R2 (e2, σ2) (e2', σ2')⌝ ={∅}=∗
        ▷ (|={∅,E}=> state_interp σ2 ∗
             spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗
             (∀ RES : val, WP e2 @ E {{ v, ∃ v', ⤇ fill K v' ∗ ⌜v = RES → v' = RES⌝ }}))
            )%I with "[-]" as "_" ; [|admit].
    give_up.
  Abort.

End pweq.
