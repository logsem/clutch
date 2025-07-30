From clutch.prob Require Import differential_privacy.
From clutch.prob_lang Require Import tactics lang notation metatheory.
From clutch.diffpriv Require Import weakestpre weakestpre_prob_lang_resources adequacy diffpriv_rules.

(* hoare_diffpriv implies approximate diffpriv *)
Fact hoare_diffpriv_pure f ε δ (εpos : (0 <= ε)%R) (δpos : (0 <= δ)%R) :
  (∀ `{diffprivGS Σ}, ⊢ hoare_diffpriv f ε δ dZ (=))
  →
    ∀ σ,
    diffpriv_approx
      (λ x y, IZR (Z.abs (x - y)))
      (λ x, lim_exec (f #x, σ))
      ε δ.
Proof.
  intros hwp ?.
  eapply (wp_diffpriv_Z diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε δ".
  tp_bind (f _).
  iApply (hwp with "[] [$f' ε δ]").
  2: erewrite 2!Rmult_1_l ; iFrame.
  1: rewrite /dZ /= -abs_IZR //.
  iNext. iIntros (??) "[-> $] //".
Qed.
