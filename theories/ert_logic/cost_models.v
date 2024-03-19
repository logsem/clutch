From clutch.ert_logic Require Import ert_weakestpre problang_wp.

Program Definition Cost1 {Λ} : Costfun Λ := (Build_Costfun (λ _, 1) _ _ _).
Next Obligation. by eexists 1. Qed.
Next Obligation. intros; simpl. lra. Qed.
Next Obligation. done. Qed. 


Section tests.

  Fixpoint at_redex {A} (f : expr → A) (e : expr) : option A :=
    let noval (e' : expr) :=
      match e' with Val _ => Some $ f e | _ => at_redex f e' end in
    match e with
    | App e1 e2      =>
        match e2 with
        | (Val v)    => noval e1
        | _          => at_redex f e2
        end
    | UnOp op e      => noval e
    | BinOp op e1 e2 =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | If e0 e1 e2    => noval e0
    | Pair e1 e2     =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | Fst e          => noval e
    | Snd e          => noval e
    | InjL e         => noval e
    | InjR e         => noval e
    | Case e0 e1 e2  => noval e0
    | AllocN e1 e2        =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end

    | Load e         => noval e
    | Store e1 e2    =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | AllocTape e    => noval e
    | Rand e1 e2     =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | _              => None
    end.

  Definition cost_app (e : expr) :=
    match e with
    | App _ _ => nnreal_one
    | _ => nnreal_zero
    end.

  Lemma costfun_bounds (b:R) (f:_->nonnegreal) e (x:nonnegreal):
    (∀ e, f e <= b)%R ->
    at_redex f e = Some x -> (x <= b)%R.
  Proof.
    intros Hbound Har.
    revert x Har. induction e; simpl; intros; try done; repeat case_match; naive_solver.
  Qed.

  Lemma costfun_pos (f:_->nonnegreal) e (x:nonnegreal):
    (∀ e, 0 <= f e)%R ->
    at_redex f e = Some x -> (0<=x)%R.
  Proof.
    intros Hbound Har.
    revert x Har. induction e; simpl; intros; try done; repeat case_match; naive_solver.
  Qed.

  Lemma costfun_fill (K:expr -> expr) `{LanguageCtx _ K} (f:_->nonnegreal) e b:
    at_redex f e = Some b -> at_redex f (K e) = Some b.
  Proof.
  Admitted.

  Program Definition Costapp : Costfun prob_lang :=
    Build_Costfun (λ e, match at_redex cost_app e with None => nnreal_zero | Some r => r end) _ _ _.
  Next Obligation.
    exists nnreal_one. intros. simpl. case_match.
    - eapply costfun_bounds; last done. intros. rewrite /cost_app. case_match; simpl; lra.
    - lra.
  Qed.
  Next Obligation.
    intros. simpl. case_match.
    - eapply costfun_pos; last done. intros; rewrite /cost_app. case_match; simpl; lra.
    - lra.
  Qed.
  Next Obligation. intros K HK. simpl. intros. Admitted.

  Definition cost_rand (e : expr) :=
    match e with
    | Rand _ _ => nnreal_one
    | _ => nnreal_zero
    end.

  Program Definition Costrand : Costfun prob_lang :=
    Build_Costfun (λ e, match at_redex cost_rand e with None => nnreal_zero | Some r => r end) _ _ _.
  Next Obligation.
    exists nnreal_one. intros. simpl. case_match.
    - eapply costfun_bounds; last done. intros. rewrite /cost_rand. case_match; simpl; lra.
    - lra.
  Qed.
  Next Obligation.
    intros. simpl. case_match.
    - eapply costfun_pos; last done. intros; rewrite /cost_rand. case_match; simpl; lra.
    - lra.
  Qed.
  Next Obligation. Admitted.

  Context `{!ert_clutchGS Σ Costapp}.


  (* #[local] Lemma test_wp_pure n :
       {{{ ⧖ (nnreal_nat (S n)) }}} #2 + #2 {{{ RET #4; ⧖ (nnreal_nat n) }}}.
     Proof.
       iIntros (?) "Hx Hp".
       wp_pure.
       by iApply "Hp".
     Qed.

     #[local] Lemma test_wp_pure' :
       {{{ ⧖ (nnreal_nat 1) }}} #2 + #2 {{{ RET #4; True }}}.
     Proof.
       iIntros (?) "Hx Hp".
       wp_pure.
       by iApply "Hp".
     Qed.

     #[local] Lemma test_wp_pures n :
       {{{ ⧖ (nnreal_nat (2 + n)) }}} #2 + #2 + #2 {{{ RET #6; ⧖ (nnreal_nat n) }}}.
     Proof.
       iIntros (?) "Hx Hp".
       wp_pures.
       by iApply "Hp".
     Qed.

     #[local] Lemma test_wp_pures' :
       {{{ ⧖ (nnreal_nat 2) }}} #2 + #2 + #2 {{{ RET #6; ⧖ (nnreal_nat 0) }}}.
     Proof.
       iIntros (?) "Hx Hp".
       wp_pures.
       by iApply "Hp".
     Qed.

     Hint Extern 0 (TCEq nnreal_one _) => rewrite nnreal_nat_1 : typeclass_instances.

     #[local] Lemma test_wp_apply :
       {{{ ⧖ (nnreal_nat 7) }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
     Proof.
       iIntros (?) "Hc H".
       (* first variant *)
       iChip "Hc" as "H1".
       wp_apply (wp_alloc with "[H1]") => //.
       iIntros (?) "Hl".
       wp_pures.
       (* second variant *)
       iChip "Hc".
       wp_apply (wp_store with "[$]").
       iIntros "Hl".
       wp_pures.
       (* third variant *)
       iChip.
       wp_apply (wp_load with "[$]").
       iIntros "_".
       by iApply "H".
     Qed.

     #[local] Lemma test_wp_heap :
       {{{ ⧖ (nnreal_nat 7) }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
     Proof.
       iIntros (?) "Hc H".
       wp_alloc ; iIntros (?) "Hl".
       wp_pures.
       wp_store ; iIntros "Hl".
       wp_pures.
       wp_load ; iIntros "Hl".
       by iApply "H".
     Qed. *)

End tests.
