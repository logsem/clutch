From clutch Require Import clutch.
From clutch.prob_lang Require Import advantage.
From clutch.prob_lang.typing Require Import tychk.

Lemma app_assoc_lr `{!clutchRGS Σ} (f g : val) (a : expr) (x : string) (α β γ : lrel Σ) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL (g (f a)) << ((λ:x, g (f (Var x))) a) : γ.
Proof.
  iIntros "aa ff gg". rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_r. case_decide ; [|done].
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.

Lemma app_assoc_lr' `{!clutchRGS Σ} (f g : val) (a : expr) (x : string) (α β γ : lrel Σ) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL ((λ:x, g (f (Var x))) a) << (g (f a)) : γ.
Proof.
  iIntros "aa ff gg". rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_l. case_decide ; [|done].
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.

Lemma app_assoc_ctx_ty (g f : val) (a : expr) (x : string) (α β γ : type) :
  ⊢ᵥ g : (β → γ) ->
  ⊢ᵥ f : (α → β) ->
  ∅ ⊢ₜ a : α ->
  ∅ ⊨ (g (f a)) =ctx= ((λ:x, g (f (Var x))) a) : γ.
Proof.
  intros.
  split ; apply (refines_sound clutchRΣ) ; intros.
  - iApply app_assoc_lr.
    + iApply refines_typed ; done.
    + replace (_ → _)%lrel with (interp (α → β) Δ) by by simpl.
      iApply refines_typed. by tychk.
    + replace (_ → _)%lrel with (interp (β → γ) Δ) by by simpl.
      iApply refines_typed. by tychk.
  - iApply app_assoc_lr'.
    + iApply refines_typed ; done.
    + replace (_ → _)%lrel with (interp (α → β) Δ) by by simpl.
      iApply refines_typed. by tychk.
    + replace (_ → _)%lrel with (interp (β → γ) Δ) by by simpl.
      iApply refines_typed. by tychk.
Qed.

Lemma app_assoc_ctx_lr (g f : val) (a : expr) (x : string) (γ : type) :
  (forall `{!clutchRGS Σ} Δ,
    exists
      (α β : lrel _),
      (⊢ REL g << g : (β → (interp γ Δ))%lrel) /\
      (⊢ REL f << f : (α → β)) /\
      (⊢ REL a << a : α)) ->
  ∅ ⊨ (g (f a)) =ctx= ((λ:x, g (f (Var x))) a) : γ.
Proof.
  intros.
  split ; apply (refines_sound clutchRΣ) ; intros.
  - destruct (H _ _ Δ) as (α & β & Hg & Hf & Ha).
    iApply (app_assoc_lr).
    + iApply Ha.
    + iApply Hf.
    + iApply Hg.
  - destruct (H _ _ Δ) as (α & β & Hg & Hf & Ha).
    iApply (app_assoc_lr').
    + iApply Ha.
    + iApply Hf.
    + iApply Hg.
Qed.

Lemma advantage_reduction_lr (adv red : val) (e e' : expr) (b : bool)
  :
  (forall `{!clutchRGS Σ},
    exists
      (α β : lrel _),
      (⊢ REL adv << adv : (β → lrel_bool)%lrel) /\
      (⊢ REL red << red : (α → β)) /\
      (⊢ REL e << e : α) /\ (⊢ REL e' << e' : α))
  ->
    (advantage adv (red e) (red e') #b <=
       advantage (λ: "v", adv (red "v")) e e' #b)%R.
Proof.
  intros.
  apply advantage_uniform.
  etrans.
  2: apply (advantage_ub _ _ _ _ σ).
  rewrite /pr_dist => /=.
  opose proof (app_assoc_ctx_lr adv red e "v" _ _) as [h h'] => //.
  { intros. destruct (H Σ _) as (α' & β' & Hadv & Hred & He & He').
    exists α', β'. split. 2: split.
    - replace (interp _ Δ) with (interp TBool Δ) by eauto. simpl. done.
    - done.
    - done.
  }
  opose proof (app_assoc_ctx_lr adv red e' "v" _ _) as [i i'] => //.
  { intros. destruct (H Σ _) as (α' & β' & Hadv & Hred & He & He').
    exists α', β'. split. 2: split.
    - replace (interp _ Δ) with (interp TBool Δ) by eauto. simpl. done.
    - done.
    - done.
  }
  rewrite /ctx_refines in h, h', i, i'.
  intros.
  simpl in h, h', i, i'.
  right. f_equal. f_equal.
  + opose proof (h [] σ b _) as hh ; [by tychk|].
    opose proof (h' [] σ b _) as hh' ; [by tychk|].
    simpl in hh, hh'.
    lra.
  + opose proof (i [] σ b _) as hh ; [by tychk|].
    opose proof (i' [] σ b _) as hh' ; [by tychk|].
    simpl in hh, hh'.
    lra.
Qed.

Lemma advantage_reduction_ty (adv red : val) (e e' : expr) (b : bool)
              (α β : type)
              (adv_typed : ⊢ᵥ adv : (β → TBool)) (red_typed : ⊢ᵥ red : (α → β))
              (e_typed : ∅ ⊢ₜ e : α) (e'_typed : ∅ ⊢ₜ e' : α)
  :
  (advantage adv (red e) (red e') #b <=
   advantage (λ: "v", adv (red "v")) e e' #b)%R.
Proof.
  apply advantage_uniform.
  etrans.
  2: apply (advantage_ub _ _ _ _ σ).
  rewrite /pr_dist => /=.
  opose proof (app_assoc_ctx_ty adv red e "v" _ _ _ _ _ _) as [h h'] => //.
  opose proof (app_assoc_ctx_ty adv red e' "v" _ _ _ _ _ _) as [i i'] => //.
  rewrite /ctx_refines in h, h', i, i'.
  intros.
  simpl in h, h', i, i'.
  right. f_equal. f_equal.
  + opose proof (h [] σ b _) as hh ; [by tychk|].
    opose proof (h' [] σ b _) as hh' ; [by tychk|].
    simpl in hh, hh'.
    lra.
  + opose proof (i [] σ b _) as hh ; [by tychk|].
    opose proof (i' [] σ b _) as hh' ; [by tychk|].
    simpl in hh, hh'.
    lra.
Qed.
