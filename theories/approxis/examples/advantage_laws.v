From clutch Require Import approxis.
From clutch.prob_lang Require Import advantage.
From clutch.prob_lang.typing Require Import tychk.


Lemma app_assoc_lr_e `{!approxisRGS Σ} (g : val) (f a : expr) (x : string) (α β γ : lrel Σ)
  (fclosed : ∀ v', (prob_lang.subst x v' f) = f)
  :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL (g (f a)) << ((λ:x, g (f (Var x))) a)%V : γ.
Proof.
  iIntros "aa ff gg". rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_r. case_decide ; [|done].
  rewrite fclosed.
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.

Lemma app_assoc_lr_e' `{!approxisRGS Σ} (g : val) (f a : expr) (x : string) (α β γ : lrel Σ)
  (fclosed : ∀ v', (prob_lang.subst x v' f) = f) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL ((λ:x, g (f (Var x))) a)%V << (g (f a)) : γ.
Proof.
  iIntros "aa ff gg". rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_l. case_decide ; [|done].
  rewrite fclosed.
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.

Lemma app_assoc_lr `{!approxisRGS Σ} (f g : val) (a : expr) (x : string) (α β γ : lrel Σ) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL (g (f a)) << ((λ:x, g (f (Var x))) a) : γ.
Proof.
  iIntros "aa ff gg".
  rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_r. case_decide ; [|done].
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.

Lemma app_assoc_lr' `{!approxisRGS Σ} (f g : val) (a : expr) (x : string) (α β γ : lrel Σ) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL ((λ:x, g (f (Var x))) a) << (g (f a)) : γ.
Proof.
  iIntros "aa ff gg". rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_l. case_decide ; [|done].
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.


Lemma app_assoc_lr_v `{!approxisRGS Σ} (f g : val) (a : expr) (x : string) (α β γ : lrel Σ) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL (g (f a)) << ((λ:x, g (f (Var x))) a)%V : γ.
Proof.
  iIntros "aa ff gg". rel_bind_l a ; rel_bind_r a ; rel_apply (refines_bind with "aa").
  iIntros (v v') "vv". rel_pures_r. case_decide ; [|done].
  rel_apply (refines_app with "gg"). rel_apply (refines_app with "ff"). rel_values.
Qed.

Lemma app_assoc_lr_v' `{!approxisRGS Σ} (f g : val) (a : expr) (x : string) (α β γ : lrel Σ) :
  (REL a << a : α) -∗
  (REL f << f : (α → β)) -∗
  (REL g << g : (β → γ)) -∗
  REL ((λ:x, g (f (Var x))) a)%V << (g (f a)) : γ.
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
  split ; apply (refines_sound approxisRΣ) ; intros.
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
  (forall `{!approxisRGS Σ} Δ,
    exists
      (α β : lrel _),
      (⊢ REL g << g : (β → (interp γ Δ))%lrel) /\
      (⊢ REL f << f : (α → β)) /\
      (⊢ REL a << a : α)) ->
  ∅ ⊨ (g (f a)) =ctx= ((λ:x, g (f (Var x))) a)%V : γ.
Proof.
  intros.
  split ; apply (refines_sound approxisRΣ) ; intros.
  - destruct (H _ _ Δ) as (α & β & Hg & Hf & Ha).
    iApply (app_assoc_lr_v).
    + iApply Ha.
    + iApply Hf.
    + iApply Hg.
  - destruct (H _ _ Δ) as (α & β & Hg & Hf & Ha).
    iApply (app_assoc_lr_v').
    + iApply Ha.
    + iApply Hf.
    + iApply Hg.
Qed.

Lemma advantage_reduction_lr (adv red : val) (e e' : expr) (b : bool)
  :
  (forall `{!approxisRGS Σ},
    exists
      (α β : lrel _),
      (⊢ REL adv << adv : (β → lrel_bool)%lrel) /\
      (⊢ REL red << red : (α → β)) /\
      (⊢ REL e << e : α) /\ (⊢ REL e' << e' : α))
  ->
    (advantage adv (red e) (red e') #b <=
       advantage (λ: "v", adv (red "v"))%V e e' #b)%R.
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

Lemma app_assoc_ctx_lr_exp (g : val) (f a : expr) (x : string) (γ : type) (fclosed : ∀ v', (prob_lang.subst x v' f) = f) :
  (forall Σ `{!approxisRGS Σ} Δ,
    exists
      (α β : lrel _),
      (⊢ REL g << g : (β → (interp γ Δ))%lrel) /\
      (⊢ REL f << f : (α → β)) /\
      (⊢ REL a << a : α)) ->
  ∅ ⊨ (g (f a)) =ctx= ((λ:x, g (f (Var x))) a)%V : γ.
Proof.
  intros h.
  split ; apply (refines_sound approxisRΣ) ; intros.
  - destruct (h _ _ Δ) as (α & β & Hg & Hf & Ha).
    iApply (app_assoc_lr_e) => //.
  - destruct (h _ _ Δ) as (α & β & Hg & Hf & Ha).
    iApply (app_assoc_lr_e') => //.
Qed.

Lemma advantage_reduction_lr_exp (adv : val) (red e e' : expr) (x : string) (b : bool) (fclosed : ∀ v', (prob_lang.subst x v' red) = red)
  :
  (forall `{!approxisRGS Σ},
    exists
      (α β : lrel _),
      (⊢ REL adv << adv : (β → lrel_bool)%lrel) /\
      (⊢ REL red << red : (α → β)) /\
      (⊢ REL e << e : α) /\ (⊢ REL e' << e' : α))
  ->
    (advantage adv (red e) (red e') #b <=
       advantage (λ: x, adv (red x))%V e e' #b)%R.
Proof.
  intros Hlr.
  apply advantage_uniform.
  etrans.
  2: apply (advantage_ub _ _ _ _ σ).
  rewrite /pr_dist => /=.
  opose proof (app_assoc_ctx_lr_exp adv red e x _ _) as [h h'] => //.
  { intros. destruct (Hlr Σ _) as (α' & β' & Hadv & Hred & He & He').
    exists α', β'. split. 2: split.
    - replace (interp _ Δ) with (interp TBool Δ) by eauto. simpl. done.
    - done.
    - done.
  }
  opose proof (app_assoc_ctx_lr_exp adv red e' x _ _) as [i i'] => //.
  { intros. destruct (Hlr Σ _) as (α' & β' & Hadv & Hred & He & He').
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

Lemma lr_advantage_aux (adversary : expr) (e e' : expr)
  (lr : ∀ `{!approxisRGS Σ} Δ, ⊢ REL adversary e << adversary e' : interp TBool Δ)
  (lr' : ∀ `{!approxisRGS Σ} Δ, ⊢ REL adversary e' << adversary e : interp TBool Δ) :
  ∀ (b : bool), (nonneg (advantage adversary e e' #b) <= 0)%R.
Proof.
  intros. apply ctx_advantage_alt. split.
  - apply (refines_sound approxisRΣ). iIntros. iApply lr.
  - apply (refines_sound approxisRΣ). iIntros. iApply lr'.
Qed.

Lemma lr_advantage (adversary : expr) (e e' : expr)
  (τ : ∀ `{!approxisRGS Σ}, lrel Σ)
  (adversary_typed : ∀ `{!approxisRGS Σ}, ⊢ REL adversary << adversary : τ → lrel_bool)
  (lr : ∀ `{!approxisRGS Σ}, ⊢ REL e << e' : τ)
  (lr' : ∀ `{!approxisRGS Σ}, ⊢ REL e' << e : τ)
  (b : bool) :
  (nonneg (advantage adversary e e' #b) <= 0)%R.
Proof.
  apply lr_advantage_aux.
  - iIntros. rel_apply refines_app. 1: iApply adversary_typed. iApply lr.
  - iIntros. rel_apply refines_app. 1: iApply adversary_typed. iApply lr'.
Qed.

Lemma lr_advantage_reflexive adversary e
  (τ : ∀ `{!approxisRGS Σ}, lrel Σ)
  (adversary_typed : ∀ `{!approxisRGS Σ}, ⊢ REL adversary << adversary : τ → lrel_bool)
  (lr : ∀ `{!approxisRGS Σ}, ⊢ REL e << e : τ)
  (b : bool) :
  (advantage adversary e e #b <= 0)%R.
Proof. eapply lr_advantage => //. Qed.

Section comp_laws.

  Context `{!approxisRGS Σ}.

  Variable (A B C D : lrel Σ).
  Variable (f g h : val).
  Variable (f_typed : ⊢ REL f << f : A → B).
  Variable (g_typed : ⊢ REL g << g : B → C).
  Variable (h_typed : ⊢ REL h << h : C → D).

  (* Definition comp {x : string} (g f : val) : val := (λ:x, g (f x))%V.
     Infix " ∘ " := comp : expr_scope. *)
  (* Use as
     rewrite -/(comp (x := "xyz") _ _). *)

  (* Definition comp : val := Λ: Λ: Λ: λ: "g" "f" "x", "g" ("f" "x").
     Infix " ∘ " := (comp #() #() #()) : expr_scope.

     Fact comp_typed : ⊢ᵥ comp : (∀:∀:∀: (#1 → #0) → (#2 → #1) → #2 → #0)%ty.
     Proof.
       rewrite /comp. do 5 constructor. tychk.
     Qed. *)

  Definition comp : val := λ: "g" "f" "x", "g" ("f" "x").
  Infix " ∘ " := comp : expr_scope.

  Fact comp_typed a b c : ⊢ᵥ comp : ((b → c) → (a → b) → a → c)%ty.
  Proof.
    rewrite /comp. tychk.
  Qed.

  Fact gf_typed : ⊢ REL g ∘ f << g ∘ f : A → C.
  Proof using (f_typed g_typed) with (rel_pures_r ; rel_pures_l).
    rewrite /comp...
    rel_arrow_val. iIntros...
    rel_bind_l (f _). rel_bind_r (f _).
    rel_apply (refines_bind with "[-]").
    - rel_apply refines_app. 1: done. rel_values.
    - iIntros. rel_apply refines_app. 1: done. rel_values.
  Qed.

  Lemma comp_assoc  :
    (⊢ REL (h ∘ (g ∘ f)) << ((h ∘ g) ∘ f) : (A → D)%lrel).
  Proof using (f_typed g_typed h_typed) with (rel_pures_r ; rel_pures_l).
    rewrite /comp...
    rel_arrow_val. iIntros...
    rel_bind_l (f _). rel_bind_r (f _).
    rel_apply (refines_bind with "[-]").
    - rel_apply refines_app. 1: done. rel_values.
    - iIntros... rel_apply refines_app. 1: done.
      rel_apply refines_app. 2: rel_values. done.
  Qed.

  Variable (a : expr).
  Variable (a_typed : ⊢ REL a << a : A).

  Goal ⊢ REL (g (f a)) << (g ∘ f) a : C.
  Proof using (f_typed g_typed a_typed) with (rel_pures_r ; rel_pures_l).
    rewrite /comp...
    rel_bind_r a ; rel_bind_l a.
    rel_apply (refines_bind $! a_typed).
    iIntros (v v') "vv"...
    rel_apply refines_app. 1: done.
    rel_apply refines_app. 2: rel_values. done.
  Qed.

End comp_laws.
