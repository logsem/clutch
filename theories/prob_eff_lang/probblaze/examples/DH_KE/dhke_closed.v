From clutch.prob_eff_lang.probblaze Require Import logic p_composition.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup def_dhke.

Section dhke_closed.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  Lemma F_AUTH_DHKE_closed : is_closed_expr ∅ (F_AUTH ∘f DH_KE).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DH_real_closed : is_closed_expr ∅ (F_AUTH ∘f C_DH_real).
  Proof. is_closed. Qed.
  Lemma F_AUTH_DHSIM_FKE_closed : is_closed_expr ∅ (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DH_rand_closed : is_closed_expr ∅ (F_AUTH ∘f C_DH_rand).
  Proof. is_closed. Qed.
  Lemma red_closed : is_closed_expr ∅ (λ: "DH", F_AUTH ∘f (λ: "f", C_lazy "DH" "f"))%E.
  Proof. is_closed. Qed.
  Lemma red_DH_real_closed : is_closed_expr ∅ ((λ: "DH", F_AUTH ∘f (λ: "f", C_lazy "DH" "f"))%E DH_real).
  Proof. is_closed. Qed.
  Lemma red_DH_rand_closed : is_closed_expr ∅ ((λ: "DH", F_AUTH ∘f (λ: "f", C_lazy "DH" "f"))%E DH_rand).
  Proof. is_closed. Qed.

End dhke_closed.
