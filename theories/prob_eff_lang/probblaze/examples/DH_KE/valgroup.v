From clutch.prelude Require Import base.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics spec_ra logic notation proofmode spec_rules class_instances metatheory.
From clutch.prob_eff_lang.probblaze.typing Require Import types. (*  interp *)
From clutch.prob_eff_lang.probblaze Require Import sem_def.
From clutch.approxis Require Import app_weakestpre.

From mathcomp Require Import solvable.cyclic choice eqtype finset fintype seq
  ssrbool ssreflect zmodp.
From mathcomp Require ssralg.
Import fingroup.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope group_scope.
Import fingroup.fingroup.
Local Notation "'cval'" := syntax.val.

Class val_group :=
  Val_group { vgG : finGroupType
            ; vgval : vgG → cval
            ; vgval_inj : Inj eq eq vgval }.

(* Both of the below seem necessary since there is a subtle difference in the
   domain type DOM, despite the two being convertible. *)
#[warning="-uniform-inheritance"] Coercion vgval_as {vg : val_group}
  (x : FinGroup.sort vgG) : cval := vgval x.
#[warning="-uniform-inheritance"] Coercion vgval_s {vg : val_group}
  (x : BaseFinGroup.sort vgG) : cval := vgval x.

Class clutch_group_struct :=
  Clutch_group_struct
    { vunit : cval
    ; vinv : cval
    ; vmult : cval
    ; veq : cval
    ; int_of_vg : cval
    ; vg_of_int : cval
    ; τG : type

    ; vunit_closed : is_closed_val vunit
    ; vinv_closed : is_closed_val vinv
    ; vmult_closed : is_closed_val vmult
    ; veq_closed : is_closed_val veq
    ; int_of_vg_closed : is_closed_val int_of_vg
    ; vg_of_int_closed : is_closed_val vg_of_int

    ; vunit_typed : val_typed vunit τG
    ; vinv_typed : val_typed vinv (τG ⇾ τG)%ty
    ; vmult_typed : val_typed vmult (τG ⇾ τG ⇾ τG)%ty
    ; veq_typed : val_typed veq (τG ⇾ τG ⇾ TBool)%ty
    ; int_of_vg_typed : val_typed int_of_vg (τG ⇾ TInt)%ty
    ; vg_of_int_typed : val_typed vg_of_int (TInt ⇾ () + τG)%ty
    }.

#[export] Hint Resolve vunit_closed : core.
#[export] Hint Resolve vinv_closed : core.
#[export] Hint Resolve vmult_closed : core.
#[export] Hint Resolve veq_closed : core.
#[export] Hint Resolve int_of_vg_closed : core.
#[export] Hint Resolve vg_of_int_closed : core.

(* In some cases (Zpˣ), we might want to use exponentiation to define
   inversion, so we expose a bare version parametrised by only the unit and
   multiplication instead of the whole group structure. *)
Definition vexp' (vunit : cval) (vmult : cval) : cval := λ:"a", rec: "vexp" "n" :=
    if: "n" ≤ #0 then vunit else let: "x" := "vexp" ("n" - #1) in vmult "a" "x".

Definition vexp `{!clutch_group_struct} : cval := vexp' vunit vmult.

Definition vexp_closed `{!clutch_group_struct} :
  is_closed_val vexp.
Proof. unfold vexp, vexp'. is_closed ; auto. Qed.

#[export] Hint Resolve vexp_closed : core.

Definition vexp_typed `{!clutch_group_struct} :
  val_typed vexp (τG ⇾ TInt ⇾ τG)%ty.
Proof.
  unfold vexp, vexp'.
(*   auto using vunit_typed, vmult_typed.
   Qed. *)
Abort.

#[export] Hint Extern 0 (val_typed vunit _) => apply vunit_typed : core.
#[export] Hint Extern 0 (val_typed vmult _) => apply vmult_typed : core.
(* #[export] Hint Extern 0 (val_typed vexp _) => apply vexp_typed : core. *)
#[export] Hint Extern 0 (val_typed int_of_vg _) => apply int_of_vg_typed : core.
#[export] Hint Extern 0 (val_typed vg_of_int _) => apply vg_of_int_typed : core.


Definition lrel_G `{probblazeRGS Σ} {vg : val_group} : sem_ty Σ
  := (λ w1 w2, ∃ a : vgG, ⌜ w1 = a ∧ w2 = a ⌝)%I.


Class clutch_group `{probblazeRGS Σ} {vg : val_group} {cg : clutch_group_struct} :=
  Clutch_group
    {
    (*   τG_lrel v1 v2 Δ : lrel_G v1 v2 ⊣⊢ interp._ty τG Δ v1 v2
       ; *) is_unit : vunit = vgval 1
    ; is_inv (x : vgG) : ⊢ WP vinv x {{ λ (v : cval), ⌜v = vgval $ x^-1⌝ }}
    ; is_spec_inv (x : vgG) K :
      ⤇ fill K (
          vinv x) -∗ spec_update ⊤ (⤇ fill K (vgval $ x^-1))
    ; is_mult (x y : vgG) : ⊢ WP vmult (vgval x) (vgval y) {{ λ (v : cval), ⌜v = vgval (x * y)%g⌝ }}
    ; is_spec_mult (x y : vgG) K :
      ⤇ fill K (vmult x y) -∗ spec_update ⊤ (⤇ fill K (vgval (x * y)%g))
    ; is_eq (x y : vgG) : ⊢ WP veq (vgval x) (vgval y) {{ λ (v : cval), ⌜v = #(bool_decide (x = y))⌝ }}
    ; is_spec_eq (x y : vgG) K : ⤇ fill K (veq (vgval x) (vgval y)) -∗ spec_update ⊤ (⤇ fill K #(bool_decide (x = y)))
    ; int_of_vg_sem : vgG -> nat
    ; int_of_vg_sem_bound : ∀ g : vgG, (int_of_vg_sem g < #|[set : vgG]|)%nat
    ; vg_of_int_sem : nat -> option vgG
    ; vg_of_int_of_vg_sem : forall (n : nat) (xg : vgG),
        vg_of_int_sem n = Some xg -> int_of_vg_sem xg = n
    ; vg_of_int_sem' : nat -> vgG
    ; BREL_INT_OF_VG_CORRECT_L := ∀ E K g X R e,
                                    (BREL (fill K #(int_of_vg_sem g)) ≤ e @ E <|X|> {{R}}) -∗
                                    (BREL (fill K (int_of_vg (vgval g))) ≤ e @ E <|X|> {{R}})
    ; BREL_INT_OF_VG_CORRECT_R := ∀ E K g X R e,
        (BREL e ≤ (fill K #(int_of_vg_sem g)) @ E <|X|> {{R}}) -∗
        (BREL e ≤ (fill K (int_of_vg (vgval g))) @ E <|X|> {{R}})
    ; brel_int_of_vg_sem_correct_l : BREL_INT_OF_VG_CORRECT_L
    ; brel_int_of_vg_sem_correct_r : BREL_INT_OF_VG_CORRECT_R
    ; BREL_VG_OF_INT_CORRECT_L :=  ∀ E K X R e x g,
                                   vg_of_int_sem x = Some g ->
                                   (BREL (fill K (SOMEV (vgval g))) ≤ e @ E <|X|> {{R}}) -∗
                                   (BREL (fill K (vg_of_int (#x))) ≤ e @ E <|X|> {{R}})
    ; brel_vg_of_int_correct_l : BREL_VG_OF_INT_CORRECT_L
    ; BREL_VG_OF_INT_CORRECT_L' := ∀ E K x X R e,
          (BREL (fill K (vgval (vg_of_int_sem' x))) ≤ e @ E <|X|> {{R}}) -∗
          (BREL (fill K (vg_of_int (#x))) ≤ e @ E <|X|> {{R}})
    ; brel_vg_of_int_correct_l' : BREL_VG_OF_INT_CORRECT_L'
    ; BREL_VG_OF_INT_CORRECT_R := ∀ E K X R e x g,
          vg_of_int_sem x = Some g ->
          (BREL e ≤ (fill K (SOMEV (vgval g))) @ E <|X|> {{R}}) -∗
          (BREL e ≤ (fill K (vg_of_int (#x))) @ E <|X|> {{R}})
    ; brel_vg_of_int_correct_r : BREL_VG_OF_INT_CORRECT_R
    ; BREL_VG_OF_INT_NONE_L := ∀ E K X R e x,
          vg_of_int_sem x = None ->
          (BREL (fill K NONEV) ≤ e @ E <|X|> {{R}}) -∗
          (BREL (fill K (vg_of_int (#x))) ≤ e @ E <|X|> {{R}})
    ; brel_vg_of_int_none_l : BREL_VG_OF_INT_NONE_L
    ; BREL_VG_OF_INT_NONE_R := ∀ E K X R e x,
          vg_of_int_sem x = None ->
          (BREL e ≤ (fill K NONEV) @ E <|X|> {{R}}) -∗
          (BREL e ≤ (fill K (vg_of_int (#x))) @ E <|X|> {{R}})
    ; brel_vg_of_int_none_r : BREL_VG_OF_INT_NONE_R

    }.

Definition vg_of_cg := λ {Σ HΣ} vg cg (G : @clutch_group Σ HΣ vg cg), vg.
Coercion vg_of_cg : clutch_group >-> val_group.

(* vg is generated by g. We further include the assumption that vg is
   nontrivial, i.e. of size at least 2, since this allows us to work with
   mathcomp's 'Z_p type of integers modulo p (taking p := #[g]). *)
Class val_group_generator {vg : val_group} :=
  Val_group_generator
    { g : vgG
    ; g_closed : is_closed_val g
    ; n'' : nat
    ; g_nontriv : #[g] = S (S n'')
    ; g_generator : generator [set: vgG] g
    }.

#[export] Hint Resolve g_closed : core.

(* The whole group is the cyclic group generated by [g], whose order is
   [S (S n'')]; hence the group cardinality is [S (S n'')]. *)
Lemma vgG_card {vg : val_group} `{!@val_group_generator vg} :
  #|[set : vgG]| = S (S n'').
Proof.
  pose proof (Is_true_eq_true _ g_generator) as Hg.
  move/eqP: Hg => ->. exact g_nontriv.
Qed.

Set Default Proof Using "Type*".

Section facts.

Context `{!probblazeRGS Σ}.

Context {vg : val_group}.
Context {cg : clutch_group_struct}.
Context {G : clutch_group (vg:=vg) (cg:=cg)}.
Context {vgg : @val_group_generator vg}.

Lemma rel_inv_l E K X R (a : vgG) t :
  (REL (fill K (Val (vgval $ a^-1)%g)) ≤ t @ E <|X|> {{R}})
    ⊢ REL  (fill K (vinv a)) ≤ t @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iApply primitive_laws.wp_bind.
  rewrite !fill_app. 
  iDestruct ("H" with "[$][$][$][$][$]") as "H".
  iApply (wp_frame_wand with "H"). iApply (wp_mono $! (is_inv a)). 
  by iIntros ; rewrite fill_app; subst.
Qed.

Lemma brel_inv_l K E X R (a : vgG) t :
   (BREL (fill K (Val (vgval $ a^-1)%g)) ≤ t @ E <|X|> {{R}})
    ⊢ BREL  (fill K (vinv a)) ≤ t @ E <|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_inv_l.
  by iApply ("Hbrel" with "[$][$]").
Qed.
  
Lemma rel_inv_r E K X R (a : vgG) t :
  (REL t ≤ (fill K (Val (vgval $ a^-1)%g)) @ E <|X|> {{R}})
    ⊢ REL t ≤ (fill K (vinv a)) @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iMod (is_spec_inv with "Hj") as "Hj". rewrite !fill_app.
  iApply ("H" with "[$][$][$][$][$]").
Qed.

Lemma brel_inv_r K E X R (a : vgG) t :
  (BREL t ≤ (fill K (Val (vgval $ a^-1)%g)) @ E <|X|> {{R}})
    ⊢ BREL t ≤ (fill K (vinv a)) @ E <|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_inv_r.
  by iApply ("Hbrel" with "[$][$]").
Qed.

Lemma rel_mult_l E K X R (a b : vgG) t :
  (REL (fill K (Val (vgval (a * b)%g))) ≤ t @ E <|X|> {{R}})
    ⊢ REL (fill K (vmult a b)) ≤ t @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iApply primitive_laws.wp_bind.
  rewrite !fill_app. 
  iDestruct ("H" with "[$][$][$][$][$]") as "H".
  iApply (wp_frame_wand with "H"). iApply (wp_mono $! (is_mult a b)). 
  by iIntros ; rewrite fill_app; subst.
Qed.

Lemma brel_mult_l K E X R (a b : vgG) t :
  (BREL (fill K (Val (vgval (a * b)%g))) ≤ t @ E <|X|> {{R}})
    ⊢ BREL (fill K (vmult a b)) ≤ t @ E<|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_mult_l.
  by iApply ("Hbrel" with "[$][$]").
Qed.

Lemma rel_mult_r E K X R (a b : vgG) t :
  (REL t ≤ (fill K (Val (vgval (a * b)%g))) @ E <|X|> {{R}})
    ⊢ REL t ≤ (fill K (vmult a b)) @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iMod (is_spec_mult with "Hj") as "Hj". rewrite !fill_app.
  iApply ("H" with "[$][$][$][$][$]").
Qed.

Lemma brel_mult_r K E X R (a b : vgG) t :
  (BREL t ≤ (fill K (Val (vgval (a * b)%g))) @ E <|X|> {{R}})
    ⊢ BREL t ≤ (fill K (vmult a b)) @ E <|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_mult_r.
  by iApply ("Hbrel" with "[$][$]").
Qed.

Lemma rel_eq_l E K X R (x y : vgG) t :
  (REL (fill K #(bool_decide (x = y))) ≤ t @ E <|X|> {{R}})
    ⊢ REL (fill K (veq x y)) ≤ t @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iApply primitive_laws.wp_bind.
  rewrite !fill_app. 
  iDestruct ("H" with "[$][$][$][$][$]") as "H".
  iApply (wp_frame_wand with "H"). iApply (wp_mono $! (is_eq x y)). 
  by iIntros ; rewrite fill_app; subst.
Qed.

Lemma brel_eq_l K E X R (x y : vgG) t :
  (BREL (fill K #(bool_decide (x = y))) ≤ t @ E <|X|> {{R}})
    ⊢ BREL (fill K (veq x y)) ≤ t @ E<|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_eq_l.
  by iApply ("Hbrel" with "[$][$]").
Qed.

Lemma rel_eq_r E K X R (x y :vgG) t :
  (REL t ≤ fill K (#(bool_decide (x = y))) @ E <|X|> {{R}})
  ⊢ REL t ≤ fill K (veq x y) @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iMod (is_spec_eq with "Hj") as "Hj". rewrite !fill_app.
  iApply ("H" with "[$][$][$][$][$]").
Qed.

Lemma brel_eq_r E K X R (x y :vgG) t :
  (BREL t ≤ fill K (#(bool_decide (x = y))) @ E <|X|> {{R}})
  ⊢ BREL t ≤ fill K (veq x y) @ E <|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_eq_r.
  by iApply ("Hbrel" with "[$][$]").
Qed.

Fact is_exp (b : vgG) (x : nat) :
  {{{ True }}} vexp b #x {{{ v, RET (v : cval); ⌜v = vgval (b ^+ x)%g⌝ }}}.
Proof.
  unfold vexp, vexp'. iIntros (? _) "hlog". 
  wp_pure. wp_pure.
  iInduction x as [|x] "IH" forall (Φ).
  - wp_pures.
    rewrite is_unit.
    iApply ("hlog").
    by rewrite expg0.
  - do 4 wp_pure.
    iApply (primitive_laws.wp_bind _ _ ((rec: _ _ := _)%V _)).
    replace (S x - 1)%Z with (Z.of_nat x) by lia.
    iApply "IH".
    iIntros. wp_pures.
    iApply (wp_frame_wand with "hlog").
    rewrite H.
    iApply (wp_mono $! (is_mult b (b ^+ x))).
    iIntros (??) "hlog" ; subst. iApply "hlog".
    by rewrite expgS.
Qed.


Fact is_spec_exp (b : vgG) (x : nat) K :
  ⤇ fill K (vexp b #x) ⊢ spec_update ⊤ (⤇ fill K (vgval (b ^+ x)%g)).
Proof.
  unfold vexp, vexp'. iIntros "hlog".
  iMod (step_pure _ _ _ _ True with "hlog") as "hlog"; [done| |].
  { eapply (logic.pure_exec_ctx [AppLCtx _] ). apply pure_beta. done. } simpl.
  iMod (step_pure _ _ _ _ True with "hlog") as "hlog"; [done| |].
  { eapply (logic.pure_exec_ctx [AppLCtx _] ). apply pure_recc. } simpl.
  iMod (step_pure _ _ _ _ True with "hlog") as "hlog"; [done|]. simpl.
  iInduction x as [|x] "IH" forall (K).
  - iMod (step_pure _ _ _ _ with "hlog") as "hlog"; [| |].
    2 : { eapply (logic.pure_exec_ctx [IfCtx _ _] ). eapply pure_binop. }
    { done. } simpl.
    iMod (step_pure _ _ _ _ with "hlog") as "hlog"; [done|].
    rewrite is_unit.
    by iModIntro.
  - iMod (step_pure _ _ _ _ with "hlog") as "hlog"; [| |].
    2 : { eapply (logic.pure_exec_ctx [IfCtx _ _] ). eapply pure_binop. }
    { done. } simpl.
    iMod (step_pure _ _ _ _ with "hlog") as "hlog"; [done|].
    iMod (step_pure _ _ _ _ with "hlog") as "hlog"; [| |].
    2 : { eapply (logic.pure_exec_ctx [AppRCtx _; AppRCtx _] ). apply pure_binop. }
    { done. } simpl.
    iMod (step_pure _ _ _ _ True with "hlog") as "hlog"; [done|simpl |].
    { eapply (logic.pure_exec_ctx [AppRCtx _]). apply pure_beta. done. } simpl.
    replace (S x - 1)%Z with (Z.of_nat x) by lia.
    iSpecialize ("IH" $! (K ++ [AppRCtx (λ: "x", vmult b "x")%E]) with "[hlog]"). { rewrite fill_app. simpl. done. }
    iMod "IH" as "IH /=". rewrite fill_app. simpl.
    iMod (step_pure _ _ _ _ True with "IH") as "IH"; [done| |].
    { apply (logic.pure_exec_ctx [AppLCtx _]). apply pure_recc. }
    iMod (step_pure _ _ _ _ True with "IH") as "IH"; [done|]. simpl.
    iDestruct (is_spec_mult with "IH") as "IH".
    by rewrite expgS.
Qed.

Lemma rel_exp_l E K X R (b : vgG) (p : nat) t :
  (REL (fill K (Val (vgval $ b ^+ p)%g)) ≤ t @ E <|X|> {{R}})
    ⊢ REL (fill K (vexp b #p)) ≤ t @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app.
  iApply primitive_laws.wp_bind.
  rewrite !fill_app. 
  iDestruct ("H" with "[$][$][$][$][$]") as "H".
  iApply (wp_frame_wand with "H"). iApply (wp_mono).
  2 : { iApply (is_exp _ _ (λ v : cval, ⌜ v = vgval (b ^+ p) ⌝)%I); first done. iIntros "!> %v %H". setoid_rewrite H. done. }
  iIntros (v ->) "Hwp". rewrite !fill_app. simpl. done.
Qed.

Lemma brel_exp_l K E X R (b : vgG) (p : nat) t :
  (BREL (fill K (Val (vgval $ b ^+ p)%g)) ≤ t @ E <|X|> {{R}})
    ⊢ BREL (fill K (vexp b #p)) ≤ t @ E <|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_exp_l.
  by iApply ("Hbrel" with "[$][$]").
Qed.
  
Lemma rel_exp_r E K X R (b : vgG) (p : nat) t :
  (REL t ≤ (fill K (Val $ vgval (b ^+ p)%g)) @ E <|X|> {{R}})
    ⊢ REL t ≤ (fill K (vexp b #p)) @ E <|X|> {{R}}.
Proof.
  iIntros "H".
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
  rewrite -!fill_app. iMod (is_spec_exp with "Hj") as "Hj". rewrite !fill_app.
  iApply ("H" with "[$][$][$][$][$]").
Qed.

Lemma brel_exp_r K E X R (b : vgG) (p : nat) t :
  (BREL t ≤ (fill K (Val $ vgval (b ^+ p)%g)) @ E <|X|> {{R}})
    ⊢ BREL t ≤ (fill K (vexp b #p)) @ E <|X|> {{R}}.
Proof.
  iIntros "Hbrel Hvalid Hdistinct".
  iApply rel_exp_r.
  by iApply ("Hbrel" with "[$][$]").
Qed.

Lemma log_g :
   ∀ v : vgG, ∃ k : fin (S (S n'')), (v = g^+k)%g.
Proof using.
  pose proof g_nontriv.
  pose proof g_generator.
  unfold generator in *.
  intros v ; destruct (@cyclePmin vgG g v).
  2: {
    assert (hx : x < #[g]%g). { apply lt_INR. rewrite Rcomplements.SSR_leq in i. lia. }
    rewrite g_nontriv in hx. apply INR_lt in hx.
    exists (nat_to_fin hx). 
    symmetry. rewrite e. f_equal.
    rewrite fin_to_nat_to_fin.
    reflexivity.
  }
  assert ([set: vgG] = cycle g)%g as <-.
  2: apply in_setT.
  by destruct (@eqtype.eqP _ [set: vgG] (cycle g)).
Qed.

End facts.


(* fast tactics to simplify inversion *)
Tactic Notation "rel_inv_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.rel _ ?e _ _ _) =>
      match e with
      | context[App (Val vinv) (Val ?a)] =>
          iApply (rel_inv_l _ _ _ _ _ _) => //
      | _ => fail "rel_inv_l: no vinv / group element found"
      end
  | _ => fail "rel_inv_l: not proving a refinement"
  end.

Tactic Notation "brel_inv_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.brel _ ?e _ _ _) =>
      match e with
      | context[App (Val vinv) (Val ?a)] =>
          iApply (brel_inv_l _ _ _ _ _ _) => //
      | _ => fail "brel_inv_l: no vinv / group element found"
      end
  | _ => fail "brel_inv_l: not proving a refinement"
  end.

Tactic Notation "rel_inv_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.rel _ _ ?e _ _) =>
      match e with
      | context[App (Val vinv) (Val ?a)] =>
          iApply (rel_inv_r _ _ _ _ _ _) => //
      | _ => fail "rel_inv_r: no vinv / group element found"
      end
  | _ => fail "rel_inv_r: not proving a refinement"
  end.

Tactic Notation "brel_inv_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.brel _ _ ?e _ _) =>
      match e with
      | context[App (Val vinv) (Val ?a)] =>
          iApply (brel_inv_r _ _ _ _ _ _) => //
      | _ => fail "brel_inv_r: no vinv / group element found"
      end
  | _ => fail "brel_inv_r: not proving a refinement"
  end.

(* fast tactics to simplify multiplications *)
Tactic Notation "rel_mult_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.rel _ ?e _ _ _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          iApply (rel_mult_l _ _ _ _ _ _ _) => //
      | _ => fail "rel_mult_l: no vmult / v1 / v2 found"
      end
  | _ => fail "rel_mult_l: not proving a refinement"
  end.

Tactic Notation "brel_mult_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.brel _ ?e _ _ _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          iApply (brel_mult_l _ _ _ _ _ _ _) => //
      | _ => fail "brel_mult_l: no vmult / v1 / v2 found"
      end
  | _ => fail "brel_mult_l: not proving a refinement"
  end.

Tactic Notation "rel_mult_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.rel _ _ ?e _ _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          iApply (rel_mult_r _ _ _ _ _ _ _) => //
      | _ => fail "rel_mult_r: no vmult / v1 / v2 found"
      end
  | _ => fail "rel_mult_r: not proving a refinement"
  end.

Tactic Notation "brel_mult_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.brel _ _ ?e _ _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          iApply (brel_mult_r _ _ _ _ _ _ _) => //
      | _ => fail "brel_mult_r: no vmult / v1 / v2 found"
      end
  | _ => fail "brel_mult_r: not proving a refinement"
  end.

(* fast tactics to simplify exponentials *)
Tactic Notation "rel_exp_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.rel _ ?e _ _ _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          iApply (rel_exp_l _ _ _ _ _ _ _) => //
      | _ => fail "rel_exp_l: no vexp / base / exponent found"
      end
  | _ => fail "rel_exp_l: not proving a refinement"
  end.

Tactic Notation "brel_exp_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.brel _ ?e _ _ _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          iApply (brel_exp_l _ _ _ _ _ _ _) => //
      | _ => fail "brel_exp_l: no vexp / base / exponent found"
      end
  | _ => fail "brel_exp_l: not proving a refinement"
  end.


Tactic Notation "rel_exp_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.rel _ _ ?e _ _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          iApply (rel_exp_r _ _ _ _ _ _ _) => //
      | _ => fail "rel_exp_r: no vexp / base / exponent found"
      end
  | _ => fail "rel_exp_r: not proving a refinement"
  end.

Tactic Notation "brel_exp_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (logic.brel _ _ ?e _ _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          iApply (brel_exp_r _ _ _ _ _ _ _) => //
      | _ => fail "brel_exp_r: no vexp / base / exponent found"
      end
  | _ => fail "brel_exp_r: not proving a refinement"
  end.


Module valgroup_tactics.
  (* Add eq tactics *)
  Ltac rel_pures :=
    iStartProof ;
    repeat (try rel_pures_r ; try first [rel_exp_r | rel_mult_r | rel_inv_r ]) ;
    repeat (try rel_pures_l ; try first [rel_exp_l | rel_mult_l | rel_inv_l ]).

  Ltac brel_pures :=
    iStartProof ;
    repeat (try brel_pures_l ; try first [brel_exp_r | brel_mult_r | brel_inv_r]) ;
    repeat (try brel_pures_r ; try first [brel_exp_l | brel_mult_l | brel_inv_l]).

  Ltac brel_pures' :=
    iStartProof ;
    repeat (first [try brel_pures_r| brel_exp_r | brel_mult_r | brel_inv_r]) ;
    repeat (first [try brel_pures_l | brel_exp_l | brel_mult_l | brel_inv_l]).


End valgroup_tactics.

Module valgroup_notation.

  Notation "e1 · e2" := (vmult e1 e2) (at level 40) : expr_scope.
  Notation "e ^-1" := (vinv e) : expr_scope.
  Notation "e1 ^ e2" := (vexp e1 e2) : expr_scope.
  Notation "e1 ^- e2" := (e1 ^ e2)^-1%E : expr_scope.

End valgroup_notation.
