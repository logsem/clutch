From discprob.basic Require Import seq_ext.
From stdpp Require Import list.
From clutch.prelude Require Import tactics.
From clutch.prob_lang Require Import erasure.
From clutch.prob Require Import couplings_dp differential_privacy.
From clutch.diffpriv Require Import diffpriv.

Set Default Proof Using "Type".


Lemma dZ_bounded_cases' x y k : (- k <= x - y ∧ x - y <= k)%Z -> (dZ x y <= (IZR k))%R.
Proof.
  rewrite /dZ/distance Rabs_Zabs. intros h. apply IZR_le. lia. 
Qed.

(** list_Z_max *)
(* x is index we are recursing
   a is prev largest value
   i is index of prev largest value
*)
Fixpoint list_Z_max' l x a i:=
  match l with
  | [] => i
  | z::zs => if bool_decide (z > a)%Z
           then list_Z_max' zs (x+1)%nat z x
           else list_Z_max' zs (x+1)%nat a i
  end.

Definition list_Z_max l :=
  match l with
  | [] => 0%nat
  | x::xs => (list_Z_max' (x::xs) 0%nat x 0%nat)
  end.

Lemma list_Z_max_cons hd tl x a i:
  list_Z_max' (hd::tl) x a i =
  if bool_decide (hd>a)%Z then
    list_Z_max' tl (x+1) hd x
  else list_Z_max' tl (x+1)%nat a i.
Proof. done. Qed. 
  
Lemma pw_list_Z_max_bound l x a i:
  i<= x -> 
  i=list_Z_max' l x a i \/ x <= list_Z_max' l x a i.
Proof.
  revert x a i.
  induction l; first naive_solver.
  simpl.
  intros x a0 i ?.
  case_bool_decide.
  - unshelve epose proof IHl (x+1) a x _; first lia.
    destruct!/=; right; lia.
  - unshelve epose proof IHl (x+1) a0 i _; first lia.
    destruct!/=; lia.
Qed.

Lemma pw_list_Z_max_bound' l x a i:
  i<x ->
  list_Z_max' l x a i < (x + length l).
Proof.
  revert x a i.
  induction l as [|hd tl IHl].
  - simpl. intros. lia.
  - simpl.
    intros. 
    case_bool_decide.
    + eapply Nat.lt_le_trans; first apply IHl; lia.
    + eapply Nat.lt_le_trans; first apply IHl; lia.
Qed.

Lemma list_Z_max_bound l:
  0<length l->
  list_Z_max l < length l.
Proof.
  intros.
  destruct l as [|z l]; first (simpl in *; lia).
  rewrite /list_Z_max.
  simpl.
  rewrite bool_decide_eq_false_2; last lia.
  eapply Nat.lt_le_trans; first apply pw_list_Z_max_bound'; lia.
Qed.   

Lemma pw_list_Z_max_after l l' x j a a' i i':
  i<= x->
  i'<=x ->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  (i=j -> a+1=a' /\ i = i')%Z ->
  (dZ a a' <=1)%R ->
  x>j ->
  list_Z_max' l x a i = j ->
  list_Z_max' l' x a' i' = j.
Proof.
  revert l' x j a a' i i'.
  induction l as [|z]; first (intros []; naive_solver).
  intros [|z' ]; first naive_solver.
  intros x j a a' i i' Hineq Hineq' Hlen H H1 H2 H3 H4.
  simpl. simpl in *.
  case_bool_decide.
  { unshelve epose proof pw_list_Z_max_bound l (x+1) z x _; lia. }
  apply dZ_bounded_cases in H2 as H5.
  case_bool_decide.
  - unshelve epose proof pw_list_Z_max_bound l (x+1) a i _ as H7; first lia.
    destruct!/=; last lia.
    exfalso.
    apply H1 in H7.
    subst.
    unshelve epose proof H (z, z') _ as H4; first (rewrite elem_of_cons; naive_solver).
    apply dZ_bounded_cases in H4. simpl in *. lia.
  - eapply IHl; last first; try done; try lia.
    intros.
    apply H.
    rewrite elem_of_cons. naive_solver.
Qed.

Lemma pw_list_Z_max_current l l' j a a' i i' z z':
  i<= j->
  i'<=j ->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  (z+1=z')%Z ->
  (i=j -> a+1=a' /\ i=i')%Z ->
  (dZ a a' <=1)%R ->
  list_Z_max' (z::l) j a i = j ->
  list_Z_max' (z'::l') j a' i' = j.
Proof.
  intros H1 H1' H2 H3 H4 H5 H6. subst.
  apply dZ_bounded_cases in H6 as H7.
  simpl. 
  intros H.
  case_bool_decide.
  - rewrite bool_decide_eq_true_2; last lia.
    eapply pw_list_Z_max_after; last first; try done; try lia.
    rewrite /dZ/=.
    replace (_-_)%Z with (-1)%Z by lia.
    by rewrite Rabs_Ropp Rabs_R1.
  - case_bool_decide.
    + rewrite Nat.le_lteq in H1. destruct H1 as []; last first.
      * unshelve epose proof H5 _; lia.
      * unshelve epose proof pw_list_Z_max_bound l (j+1) a i _ as H8; first lia.
        destruct H8; last lia.
        assert (i=j) as -> by congruence.
        lia.
    + eapply pw_list_Z_max_after; last first; try done; lia.
Qed. 

Lemma pw_list_Z_max_before l l' i i' x z a a' j:
  i<= x->
  (i'<=j)%nat ->
  (x<=j) ->
  length l = length l' ->
  (l!!(j-x)=Some z) ->
  (l'!!(j-x)=Some (z+1)%Z)->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  (i=j -> a+1=a'/\i'=j)%Z ->
  (dZ a a' <=1)%R ->
  list_Z_max' (l) x a i = j ->
  list_Z_max' (l') x a' i' = j.
Proof.
  revert l' i i' x z a a' j.
  induction l as [|hd tl IHl]; first (by intros []).
  intros [|hd' tl']; first done.
  intros i i' x z a a' j H1 H1' H2 H3 H4 H5 H6 H7 H8 H9.
  rewrite Nat.le_lteq in H2.
  destruct H2 as [|<-]; last first.
  { eapply pw_list_Z_max_current; last done; try done.
    - by simplify_eq.
    - intros. apply H6.
      simpl.
      rewrite elem_of_cons. naive_solver.
    - rewrite Nat.sub_diag in H5 H4.
      simpl in *. by simplify_eq.
    - intros. naive_solver.
  }
  simpl in *.
  case_bool_decide.
  { unshelve epose proof pw_list_Z_max_bound tl (x+1) hd x _ as H10; first lia.
    destruct H10; first lia.
    case_bool_decide.
    - eapply IHl; last done; try done; try lia.
      + rewrite lookup_cons_Some in H4.
        rewrite Nat.sub_add_distr.
        destruct H4; first lia.
        naive_solver.
      + rewrite lookup_cons_Some in H5.
        rewrite Nat.sub_add_distr.
        destruct H5; first lia.
        naive_solver.
      + intros.
        apply H6. rewrite elem_of_cons; naive_solver.
      + unshelve epose proof H6 (hd, hd') _; last done.
        rewrite elem_of_cons. naive_solver.
    - eapply IHl; last done; last first; try done; try lia.
      + unshelve epose proof H6 (hd, hd') _ as H11; first (rewrite elem_of_cons; naive_solver).
        simpl in *.
        apply dZ_bounded_cases in H8, H11.
        rewrite Rcomplements.Rabs_le_between.
        split.
        * replace (-(1))%R with (IZR (-1))%Z by done.
          apply IZR_le. lia.
        * apply IZR_le. lia.
      + intros.
        apply H6. rewrite elem_of_cons; naive_solver.
      + rewrite lookup_cons_Some in H5.
        rewrite Nat.sub_add_distr.
        destruct H5; first lia.
        naive_solver.
      + rewrite lookup_cons_Some in H4.
        rewrite Nat.sub_add_distr.
        destruct H4; first lia.
        naive_solver.
  }
  case_bool_decide.
  - eapply IHl; last done; try lia.
    + rewrite lookup_cons_Some in H4.
      rewrite Nat.sub_add_distr.
      destruct H4; first lia.
      naive_solver.
    + rewrite lookup_cons_Some in H5.
      rewrite Nat.sub_add_distr.
      destruct H5; first lia.
      naive_solver.
    + intros.
      apply H6. rewrite elem_of_cons; naive_solver.
    + unshelve epose proof H6 (hd, hd') _ as H11; first (rewrite elem_of_cons; naive_solver).
        simpl in *.
        apply dZ_bounded_cases in H8, H11.
        rewrite Rcomplements.Rabs_le_between.
        split.
        * replace (-(1))%R with (IZR (-1))%Z by done.
          apply IZR_le. lia.
        * apply IZR_le. lia.
  - eapply IHl; last done; try lia.
    + rewrite lookup_cons_Some in H4.
      rewrite Nat.sub_add_distr.
      destruct H4; first lia.
      naive_solver.
    + rewrite lookup_cons_Some in H5.
      rewrite Nat.sub_add_distr.
      destruct H5; first lia.
      naive_solver.
    + intros.
      apply H6. rewrite elem_of_cons; naive_solver.
    + unshelve epose proof H6 (hd, hd') _ as H11; first (rewrite elem_of_cons; naive_solver).
        simpl in *.
        apply dZ_bounded_cases in H8, H11.
        rewrite Rcomplements.Rabs_le_between.
        split.
        * replace (-(1))%R with (IZR (-1))%Z by done.
          apply IZR_le. lia.
        * apply IZR_le. lia.
Qed. 
  
  
Lemma pw_list_Z_max_correct l l' z (j:nat):
  length l > 0 ->
  length l = length l' -> 
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  (l!!(j)=Some z) ->
  (l'!!(j)=Some (z+1)%Z)->
  list_Z_max l = j ->
  list_Z_max l' = j.
Proof.
  destruct l; first (simpl; lia).
  destruct l'; first done.
  rewrite /list_Z_max.
  intros H1 H2 H3 H4 H5 H6.
  eapply pw_list_Z_max_before; last done; try done; try lia.
  - by rewrite Nat.sub_0_r. 
  - by rewrite Nat.sub_0_r.
  - intros H. subst.
    split; last done.
    rewrite -H in H5, H4.
    simpl in *. by simplify_eq.
  - unshelve epose proof H3 (_,_) _ as K; last apply K.
    rewrite elem_of_cons. naive_solver.
Qed. 

(** laplace_map *)
Fixpoint laplace_map num den (Hproof:(0<IZR num / IZR den)%R) (l:list Z) :=
  match l with
  | [] => dret []
  | loc::l' =>
      dbind (λ z,
               dbind (λ zs, dret (z::zs)) (laplace_map num den Hproof l')
        ) (laplace_rat num den loc)
  end.

Lemma laplace_map_pos num den Hproof l zs:
  (laplace_map num den Hproof l zs > 0)%R ->
  length zs = length l.
Proof.
  revert zs.
  induction l as [|?? IHl]; intros zs; simpl; intros H; inv_distr; first done.
  all: erewrite <-IHl; done.
Qed.

Lemma laplace_map_mass num den Hproof l :
  (SeriesC (laplace_map num den Hproof l) =1)%R.
Proof.
  induction l as [|? ? IHl]; first (simpl; solve_distr_mass).
  simpl.
  setoid_rewrite dbind_mass.
  erewrite SeriesC_ext; last first.
  { intros. rewrite dbind_mass.
    erewrite SeriesC_ext; last first.
    - intros. rewrite dret_mass.
      by rewrite Rmult_1_r.
    - rewrite IHl. by rewrite Rmult_1_r.
  }
  solve_distr_mass.
Qed.

Lemma ineq_convert num den:
  (0 < IZR num / IZR (2 * den))%R ->
  (0 < IZR num / IZR (den))%R.
Proof.
  intros.
  rewrite mult_IZR in H. 
  rewrite Rdiv_mult_distr in H. lra.
Qed. 

Fact Mcoupl_laplace_rat_isometry (num den loc loc' : Z) :
  Mcoupl (laplace_rat num den loc) (laplace_rat num den loc') (λ z z', z - z' = loc - loc')%Z 0.
Proof.
  intros ?? Hf Hg Hfg.
  rewrite exp_0. ring_simplify.
  rewrite -(SeriesC_translate _ (loc - loc')).
  2:{ intros. apply Rmult_le_pos. 1: auto. apply Hf. }
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace_rat num den loc)).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hf.
      - destruct (Hf z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  apply SeriesC_le.
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace_rat num den loc')).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hg.
      - destruct (Hg z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  intros z. split.
  { apply Rmult_le_pos => //. apply Hf. }
  opose proof (Hfg ((z + (loc - loc'))) z _)%Z.
  1: lia.
  apply Rmult_le_compat => //.
  1: apply Hf.
  rewrite /laplace_rat/laplace/laplace'/pmf{1 3}/laplace_f/laplace_f_nat.
  right.
  case_decide.
  1: do 7 f_equal ; lia.
  simpl. rewrite /dret_pmf. repeat case_bool_decide ; try lra. 1,2: qify_r ; zify_q.
  1,2: lia.
Qed.

Lemma laplace_map_pw_after num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (laplace_map num (2*den) (Hproof) l)
    (laplace_map num (2*den) (Hproof) l')
    (λ zs zs',
       length zs = length zs' /\
       (∀ p, p ∈ zip_with (λ x y, (x,y)) zs zs' -> (dZ p.1 p.2 <= 1)%R) 
    ) 0 0.
Proof.
  revert l'.
  induction l as [|hd tl IHl].
  - intros []; last done.
    simpl.
    intros.
    apply DPcoupl_dret; naive_solver.
  - intros [|hd' tl']; first done.
    simpl.
    intros H1 H2.
    replace 0%R with (0+0)%R by lra.
    unshelve epose proof H2 (hd, hd') _ as H3.
    { rewrite elem_of_cons; naive_solver. }
    apply dZ_bounded_cases in H3 as H4.
    eapply (DPcoupl_dbind _ _ _ _ (λ z z', (dZ z z' <= 1)%R)); try done; last first.
    { eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl; last apply Mcoupl_laplace_rat_isometry; try done.
      intros.
      apply dZ_bounded_cases'. simpl in *. lia.
    }
    intros z z' Hz.
    replace 0%R with (0+0)%R by lra.
    eapply DPcoupl_dbind; last apply IHl; try done; last first.
    + intros. apply H2. rewrite elem_of_cons; naive_solver.
    + by simplify_eq.
    + simpl.
      intros ??[H5 H6].
      apply DPcoupl_dret; try done.
      split; first (simpl; lia).
      simpl.
      intros [].
      rewrite elem_of_cons.
      intros [|]; simplify_eq; naive_solver.
Qed.


Lemma laplace_map_pw num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R) j:
  length l = length l' ->
  (length l > 0)%nat ->
  (j<length l)%nat->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (laplace_map num (2*den) (Hproof) l)
    (laplace_map num (2*den) (Hproof) l')
    (λ zs zs',
       length zs > 0 /\
       length zs = length zs' /\
       (∀ p, p ∈ zip_with (λ x y, (x,y)) zs zs' -> (dZ p.1 p.2 <= 1)%R) /\
       ∃ (z: Z),
         zs!!j=Some z /\ zs' !!j = Some (z+1)%Z
    ) (IZR num / IZR den) 0.
Proof.
  revert l l'.
  induction j as [|? Hj].
  - replace 0%R with (0+0)%R by lra.
    replace (_/_)%R with (IZR num / IZR den + 0)%R by lra.
    intros [|hd tl] [|hd' tl']; simpl; try lia.
    intros H1 H2 H3 H4.
    simplify_eq.
    eapply (DPcoupl_dbind _ _ _ _ (λ z z', z+1=z')%Z); try done; last first.
    { rewrite /laplace_rat. case_decide ; [|done].
      eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl; last eapply (Mcoupl_laplace_alt _ _ _ 1); try done.
      simpl.
      rewrite mult_IZR.
      replace (_/(_*_))%R with (/2 * (IZR num / IZR den))%R; last (rewrite Rdiv_mult_distr; lra).
      rewrite -Rmult_assoc.
      rewrite -{2}(Rmult_1_l (_/_)%R).
      apply Rmult_le_compat_r.
      - left. by apply ineq_convert.
      - unshelve epose proof H4 (hd, hd') _ as H5.
        + rewrite elem_of_cons; naive_solver.
        + cut (IZR (Z.abs (1 + hd - hd')) <=2)%R; first lra.
          rewrite -Rabs_Zabs.
          apply dZ_bounded_cases'.
          apply dZ_bounded_cases in H5. simpl in *. lia.
    }
    intros ?? <-.
    replace 0%R with (0+0)%R by lra.
    eapply DPcoupl_dbind; last apply laplace_map_pw_after; try done; last first.
    { intros. apply H4. rewrite elem_of_cons; naive_solver. }
    simpl.
    intros ??[].
    apply DPcoupl_dret; try done.
    repeat split; simpl; try lia; last naive_solver.
    intros [].
    rewrite elem_of_cons.
    intros []; simplify_eq; last naive_solver.
    apply dZ_bounded_cases'. simpl. lia.
  - intros [|hd tl] [|hd' tl']; simpl; try lia.
    intros H1 H2 H3 H4.
    simplify_eq.
    replace 0%R with (0+0)%R by lra.
    replace (_/_)%R with (0+IZR num / IZR den)%R by lra.
    eapply (DPcoupl_dbind _ _ _ _ (λ z z', (dZ z z' <= 1)%R)); try done; last first.
    { rewrite /laplace_rat. case_decide ; [|done].
      eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl; last eapply (Mcoupl_laplace_isometry); try done.
      simpl.
      intros ?? ->.
      unshelve epose proof H4 (_,_) _ as H5; last apply H5.
      rewrite elem_of_cons. naive_solver.
    }
    intros ???.
    replace 0%R with (0+0)%R by lra.
    replace (_/_)%R with (IZR num / IZR den+0)%R by lra.
    eapply DPcoupl_dbind; last apply Hj; try done; try lia; last first. 
    + intros. apply H4. rewrite elem_of_cons; naive_solver.
    + simpl.
      intros. destruct!/=.
      apply DPcoupl_dret; try done; simpl.
      repeat split; try lia.
      * intros []. rewrite elem_of_cons. intros. destruct!/=; naive_solver.
      * naive_solver.
Qed.

Lemma laplace_map_correct' num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (length l > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (laplace_map num (2*den) (Hproof) l)
    (laplace_map num (2*den) (Hproof) l')
    (λ zs zs', list_Z_max zs = list_Z_max zs'
    ) (IZR num / IZR den) 0.
Proof.
  intros Ha Hb Hc.
  replace 0%R with (SeriesC (λ (x:nat), 0)); last by apply SeriesC_0.
  apply DPcoupl_pweq'.
  - pose proof (ineq_convert _ _ Hproof) as K. lra.
  - done.
  - apply ex_seriesC_0.
  - intros j.
    destruct (decide (j<length l)); last first.
    {
      eapply DPcoupl_mono; last eapply DPcoupl_pos_R; last eapply DPcoupl_trivial; try done.
      - simpl. intros ? ? [? [?%laplace_map_pos ?]].
        intros. subst.
        unshelve epose proof list_Z_max_bound x _; lia.
      - left. by apply ineq_convert.
      - apply laplace_map_mass.
      - apply laplace_map_mass.
    }
    eapply DPcoupl_mono; last eapply DPcoupl_pos_R; last eapply laplace_map_pw; try done.
    simpl.
    intros ?? [H [Hlen%laplace_map_pos Hlen'%laplace_map_pos]]?.
    destruct!/=. eapply pw_list_Z_max_correct; naive_solver.
Qed. 

Lemma laplace_map_correct num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (length l > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (laplace_map num (2*den) (Hproof) l)
    (laplace_map num (2*den) (Hproof) l')
    (λ zs zs', length zs = length zs' /\ (length zs = length l)%nat /\
               list_Z_max zs = list_Z_max zs'
    ) (IZR num / IZR den) 0.
Proof.
  intros.
  eapply DPcoupl_mono; last (eapply DPcoupl_pos_R; eapply laplace_map_correct'); try done.
  intros ??[?[?%laplace_map_pos ?%laplace_map_pos]]. lia.
Qed.

Fixpoint laplace_presample_list σ ls:=
  match ls with
  | [] => dret σ
  | hd :: tl => dbind (λ σ', laplace_presample_list σ' tl) (state_step_laplace σ hd)
  end.

Fixpoint replace_laplace_tape num den σ ls :=
  match ls with
  | [] => σ
  | hd::tl =>
      let '(ι, mean, ls, z) :=hd in
        state_upd_tapes_laplace <[ι := Tape_Laplace num den mean (ls++[z])]> (replace_laplace_tape num den σ tl)
  end.

Lemma laplace_presample_list_rewrite_notin l tl x σ num den :
  l ∉ tl.*1.*1.*1 ->
  replace_laplace_tape num den (state_upd_tapes_laplace <[l:=x]> σ)
    tl =
  state_upd_tapes_laplace <[l:=x]>
    (replace_laplace_tape num den σ tl).
Proof.
  induction tl; first naive_solver.
  rewrite !fmap_cons.
  destruct a as [[[]]].
  rewrite elem_of_cons.
  intros Hcontra.
  simpl.
  rewrite IHtl; last naive_solver.
  simpl.
  f_equal.
  rewrite insert_commute; first done.
  naive_solver.
Qed. 

Lemma laplace_presample_list_rewrite num den l σ (Hproof: (0 < IZR num / IZR (2*den))%R):
  Forall (λ '(ι, loc, lis), tapes_laplace σ!!ι = Some (Tape_Laplace num (2*den) loc lis)) l ->
  NoDup (l.*1.*1) ->
  laplace_presample_list σ ((l.*1).*1) =
  dbind (λ zs,
           dret (replace_laplace_tape num (2*den) σ (zip l zs))
    ) (laplace_map num (2*den) (Hproof) (l.*1.*2))
.
Proof.
  revert σ.
  induction l as [|hd tl IHl].
  { simpl. intros. by rewrite dret_id_left. }
  intros σ Hforall Hnodup.
  destruct hd as [[]].
  rewrite !fmap_cons.
  rewrite /laplace_presample_list.
  etrans.
  { simpl.
    rewrite Forall_cons in Hforall.
    erewrite state_step_laplace_unfold; last naive_solver.
    rewrite /dmap.
    eapply dbind_ext_right_strong.
    intros σ' Hpos.
    apply dbind_pos in Hpos.
    destruct!/=.
    inv_distr; last naive_solver.
    erewrite IHl; last first.
    - apply NoDup_cons in Hnodup. naive_solver.
    - apply NoDup_cons in Hnodup as [Hnodup _]. revert H2 Hnodup.
      clear.
      induction tl as [|[[]] ? IHtl]; first by rewrite !Forall_nil.
      rewrite !Forall_cons.
      intros. destruct!/=.
      split.
      + rewrite lookup_insert_ne; first done.
        rewrite elem_of_cons in Hnodup. naive_solver.
      + apply IHtl; first done.
        rewrite elem_of_cons in Hnodup.
        naive_solver.
    - rewrite dmap_fold.
      instantiate (1:=λ x, dmap
                        (λ a0 : list Z,
                           replace_laplace_tape num (2*den)
                             x
                             (zip tl a0))
                        (laplace_map num (2*den) Hproof tl.*1.*2)).
      done.
  }
  rewrite /laplace_map.
  rewrite -/laplace_map.
  rewrite -!dbind_assoc'.
  apply dbind_ext_right.
  intros z'.
  rewrite /dmap.
  rewrite dret_id_left.
  rewrite -dbind_assoc'.
  apply dbind_ext_right_strong.
  intros ? Hpos.
  apply laplace_map_pos in Hpos.
  rewrite dret_id_left.
  simpl. f_equal.
  rewrite laplace_presample_list_rewrite_notin; first done.
  rewrite !length_fmap in Hpos.
  rewrite fst_zip; last lia.
  simpl in Hnodup.
  apply NoDup_cons in Hnodup.
  naive_solver.
Qed. 

(* ls a list of tape loc content*)

Lemma replace_laplace_tape_zip ls zs num den σ:
  length ls = length zs ->
  NoDup (ls.*1.*1) ->
  Forall
    (λ '(ι, loc, lis, z),
       tapes_laplace (replace_laplace_tape num (2 * den) σ (zip ls zs)) !! ι =
       Some (Tape_Laplace num (2 * den) loc (lis ++ [z])))
    (zip ls zs).
Proof.
  revert zs σ.
  induction ls as [|[[]]? IHl].
  { simpl. intros. by apply Forall_nil. }
  intros [|z']?; first (simpl; lia).
  rewrite !fmap_cons.
  intros H1 H2.
  simpl in H1, H2.
  simplify_eq.
  apply NoDup_cons in H2.
  rewrite /zip-/zip.
  apply Forall_cons.
  split.
  - simpl.
    by rewrite lookup_insert.
  - epose proof IHl _ (state_upd_tapes_laplace <[_:=_]> σ) _ _ as H.
    eapply Forall_impl; first done.
    intros [[[]]].
    rewrite laplace_presample_list_rewrite_notin; first done.
    rewrite fst_zip; first naive_solver.
    lia.
    Unshelve.
    + lia.
    + naive_solver.
Qed. 

Lemma laplace_state_list_coupl num den ls ls' σ σ':
  (0 < IZR num / IZR (2 * den))%R -> 
  length ls = length ls' ->
  (length ls > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x.1.2,y.1.2)) ls ls' -> (dZ p.1 p.2 <= 1)%R) ->
  (NoDup ls.*1.*1) ->
  (NoDup ls'.*1.*1) ->
  Forall (λ '(ι, loc, lis), tapes_laplace σ!!ι = Some (Tape_Laplace num (2*den) loc lis)) ls ->
  Forall (λ '(ι, loc, lis), tapes_laplace σ'!!ι = Some (Tape_Laplace num (2*den) loc lis)) ls' ->
  DPcoupl (laplace_presample_list σ ls.*1.*1)
    (laplace_presample_list σ' ls'.*1.*1)
    (λ σf σf',
       ∃ zs zs', length zs = length zs' /\ (length zs = length ls)%nat /\
                 list_Z_max zs = list_Z_max zs' /\
                 σf = (replace_laplace_tape num (2 * den) σ (zip ls zs)) /\ 
                 σf' = (replace_laplace_tape num (2 * den) σ' (zip ls' zs'))(*  /\  *)
                 (* Forall (λ '(ι, loc, lis, z), tapes_laplace σf!!ι = Some (Tape_Laplace num (2*den) loc (lis ++ [z]))) (zip ls zs) /\ *)
                 (* Forall (λ '(ι, loc, lis, z), tapes_laplace σf'!!ι = Some (Tape_Laplace num (2*den) loc (lis ++ [z]))) (zip ls' zs') *)
    ) (IZR num / IZR den) 0.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8.
  unshelve (repeat erewrite laplace_presample_list_rewrite); last first; try done.
  replace (0)%R with (0+0)%R by lra.
  replace (_/_)%R with (IZR num / IZR den + 0)%R by lra.
  eapply DPcoupl_dbind; [done|done| |apply laplace_map_correct]; last first.
  - repeat setoid_rewrite zip_with_fmap_l.
    repeat setoid_rewrite zip_with_fmap_r. naive_solver.
  - rewrite !length_fmap. lia.
  - rewrite !length_fmap. lia.
  - simpl.
    rewrite !length_fmap.
    intros zs zs' (?&?&?).
    apply DPcoupl_dret; try done.
    exists zs, zs'.
    repeat split; lia. 
Qed. 

Lemma laplace_presample_list_erasable num den σ ls (Hineq:(0 < IZR num / IZR (2 * den))%R):
  NoDup ls.*1.*1->
  Forall (λ '(ι, loc, lis), tapes_laplace σ!!ι = Some (Tape_Laplace num (2*den) loc lis)) ls ->
  erasable (laplace_presample_list σ ls.*1.*1) σ.
Proof.
  revert σ.
  induction ls as [|[[]] tl IHls]; intros ? Hnodup H; first apply dret_erasable.
  simpl.
  apply erasable_dbind.
  - eapply state_step_laplace_erasable.
    rewrite Forall_cons in H. naive_solver.
  - intros ? Hpos. apply IHls.
    { rewrite !fmap_cons in Hnodup.
      rewrite NoDup_cons in Hnodup.
      naive_solver.
    }
    rewrite Forall_cons in H.
    destruct!/=.
    rewrite /state_step_laplace in Hpos.
    case_bool_decide as H; last first. 
    { rewrite elem_of_dom in H.
      naive_solver.
    }
    setoid_rewrite lookup_total_correct in Hpos; last done.
    simpl in *.
    inv_distr; last lra.
    simpl.
    clear -H1 Hnodup.
    apply NoDup_cons in Hnodup as [Hnodup _].
    revert H1 Hnodup.
    induction tl.
    + intros. by apply Forall_nil.
    + rewrite Forall_cons.
      intros. destruct!/=.
      rewrite Forall_cons; split.
      * rewrite lookup_insert_ne; first done.
        rewrite elem_of_cons in Hnodup. naive_solver.
      * apply IHtl; first done.
        rewrite elem_of_cons in Hnodup. naive_solver.
Qed.

Lemma replace_laplace_tape_heap num den h t l ls:
  (heap (replace_laplace_tape num (2 * den)
                              {| heap := h; tapes := t; tapes_laplace := l |} ls) = h).
Proof.
  revert h t l.
  induction ls; first naive_solver.
  intros. simpl.
  repeat case_match; subst.
  simpl.
  naive_solver.
Qed. 

Lemma replace_laplace_tape_tapes num den h t l ls:
  (tapes (replace_laplace_tape num (2 * den)
                              {| heap := h; tapes := t; tapes_laplace := l |} ls) = t).
Proof.
  revert h t l.
  induction ls; first naive_solver.
  intros. simpl.
  repeat case_match; subst.
  simpl.
  naive_solver.
Qed.

Section coupling_rule.
  Context `{!diffprivGS Σ}.
  
  Lemma hoare_couple_laplace_list_update xιs xιs' zs zs' ls ls' σ σ' num den:
    length xιs = length xιs' -> 
    NoDup xιs.*2 -> NoDup xιs'.*2 ->
    length zs = length xιs ->
    length zs' = length xιs ->
    ls = zip (zip xιs.*2 xιs.*1) (replicate (length xιs) []) ->
    ls' =zip (zip xιs'.*2 xιs'.*1) (replicate (length xιs) []) ->
    tapes_laplace_auth 1 (tapes_laplace σ) -∗
    spec_tapes_laplace_auth (tapes_laplace σ') -∗
    ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪L (num,2 * den,x; []) ∗
            ι' ↪Lₛ (num,2 * den,x'; []) ∗ ⌜(Rabs (IZR (x - x')) <= 1)%R⌝)
    ==∗
    (tapes_laplace_auth 1 (tapes_laplace (replace_laplace_tape num (2 * den) σ (zip ls zs)))) ∗
     spec_tapes_laplace_auth (tapes_laplace (replace_laplace_tape num (2 * den) σ' (zip ls' zs'))) ∗
    ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪L (num,2 * den,x; [
                                                    zs !!! k]) ∗ ι' ↪Lₛ (num,2 * den,x'; [zs' !!! k]) ∗ ⌜(Rabs (IZR (x - x')) <= 1)%R⌝).
  Proof.
    revert xιs' zs zs' ls ls' σ σ'.
    induction xιs as [|hd xιs IH].
    {
      intros []; last (simpl; lia).
      intros []; last (simpl; lia).
      intros []; last (simpl; lia).
      simpl.
      intros.
      subst. simpl.
      iIntros.
      by iFrame.
    }
    simpl.
    intros [|? xιs']; first (simpl; lia).
    intros [|? zs]; first (simpl; lia).
    intros [|? zs']; first (simpl; lia).
    simpl.
    intros ls ls' σ σ'.
    intros H1 H2 H3 H4 H5 -> ->.
    rewrite !NoDup_cons in H2, H3.
    iIntros "H1 H2 H3".
    case_match. case_match; subst.
    iDestruct "H3" as "(H3 & H4)".
    iMod (IH xιs' zs zs' _ _ σ σ' with "[$][$][$]") as "H".
    - lia.
    - naive_solver.
    - naive_solver.
    - lia.
    - lia.
    - done.
    - done.
    - iDestruct ("H3") as "(H1&H2&%)".
      iDestruct "H" as "(H3&H4&H5)".
      simpl.
      iMod (ghost_map_update with "H3 H1") as "[$ $]".
      iMod (ghost_map_update with "H4 H2") as "[$ $]".
      iModIntro.
      iSplit; first done.
      iFrame.
  Qed. 
  
  Lemma hoare_couple_laplace_list num den xιs xιs' N e Φ:
    (0 < IZR num / IZR (2 * den))%R ->
    length xιs = N ->
    length xιs = length xιs' ->
    (length xιs > 0)%nat ->
    NoDup xιs.*2 -> NoDup xιs'.*2 ->
           ↯m (IZR num / IZR den) -∗
           ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪L (num, 2 * den,x; []) ∗ ι' ↪Lₛ (num,2 * den,x'; []) ∗ ⌜(dZ x x' <= 1)%R⌝) -∗
             ((∃ zs zs', ([∗ list] k ↦ '(x, ι);'(x', ι') ∈ xιs;xιs',
                            ι ↪L (num, 2 * den,x; [zs !!! k]) ∗
                            ι' ↪Lₛ (num,2 * den,x'; [zs' !!! k]) ∗
                            ⌜(dZ x x' <= 1)%R⌝) ∗
                         ⌜length zs = N⌝ ∗
                         ⌜length zs' = N⌝ ∗
                         ⌜list_Z_max zs = list_Z_max zs'⌝)
              -∗
              WP e {{ v, Φ v }})
             -∗
               WP e {{ v, Φ v }}.
  Proof.
    iIntros (Hineq Hlen1 Hlen2 Hlen3 Hnodup1 Hnodup2) "Herr Hlist HΦ".
    iApply wp_lift_step_spec_couple.
    iIntros (σ e' σ' ε δ) "((Hh1 & Ht1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Htl2)/=".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Herr") as %(ε'' & ε_now_rest & foo & Hε'').
    set (ls := zip (zip xιs.*2 xιs.*1) (replicate N ([]:list Z))).
    set (ls' := zip (zip xιs'.*2 xιs'.*1) (replicate N ([]:list Z))).
    iAssert (⌜Forall (λ '(ι, loc, lis), tapes_laplace σ!!ι = Some (Tape_Laplace num (2*den) loc lis)) ls⌝)%I as "%".
    { rewrite List.Forall_forall.
      iIntros ([[??]?]).
      rewrite -elem_of_list_In.
      rewrite /ls.
      rewrite elem_of_list_lookup.
      iIntros ([k Hsome]).
      rewrite big_sepL2_alt.
      iDestruct "Hlist" as "[_ Hlist]".
      repeat rewrite lookup_zip_Some in Hsome.
      assert (is_Some (zip (zip xιs'.*2 xιs'.*1) (replicate N ([]:list Z)) !! k)).
      { eapply lookup_lt_is_Some_2.
        rewrite !length_zip !length_fmap length_replicate.
        destruct Hsome as [Hsome1 Hsome2].
        apply lookup_replicate in Hsome2.
        lia.
      }
      destruct H as [[[]] H].
      repeat rewrite lookup_zip_Some in H.
      destruct Hsome as [[H1 H2] H3].
      destruct H as [[H4 H5] H6].
      rewrite !list_lookup_fmap in H1, H2, H4, H5.
      rewrite !lookup_replicate in H3, H6. 
      simpl in *.
      destruct!/=.
      destruct (xιs!!k) as [[]|] eqn:K1; try done.
      destruct (xιs'!!k) as [[]|] eqn:K2; try done.
      simpl in *.
      simplify_eq.
      eassert (_∈zip xιs xιs') as H.
      { eapply elem_of_list_lookup_2.
        erewrite lookup_zip_Some. naive_solver.
      }
      iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
      simpl.
      iDestruct "H" as "[H ?]".
      by iDestruct (ghost_map_lookup with "Htl1 H") as "%".
    }
    iAssert (⌜Forall (λ '(ι, loc, lis), tapes_laplace σ'!!ι = Some (Tape_Laplace num (2*den) loc lis)) ls'⌝)%I as "%".
    { rewrite List.Forall_forall.
      iIntros ([[??]?]).
      rewrite -elem_of_list_In.
      rewrite /ls.
      rewrite elem_of_list_lookup.
      iIntros ([k Hsome]).
      rewrite big_sepL2_alt.
      iDestruct "Hlist" as "[_ Hlist]".
      repeat rewrite lookup_zip_Some in Hsome.
      assert (is_Some (zip (zip xιs.*2 xιs.*1) (replicate N ([]:list Z)) !! k)) as H'.
      { eapply lookup_lt_is_Some_2.
        rewrite !length_zip !length_fmap length_replicate.
        destruct Hsome as [Hsome1 Hsome2].
        apply lookup_replicate in Hsome2.
        lia.
      }
      destruct H' as [[[]] H'].
      repeat rewrite lookup_zip_Some in H'.
      destruct Hsome as [[H1 H2] H3].
      destruct H' as [[H4 H5] H6].
      rewrite !list_lookup_fmap in H1, H2, H4, H5.
      rewrite !lookup_replicate in H3, H6. 
      simpl in *.
      destruct!/=.
      destruct (xιs!!k) as [[]|] eqn:K1; try done.
      destruct (xιs'!!k) as [[]|] eqn:K2; try done.
      simpl in *.
      simplify_eq.
      eassert (_∈zip xιs xιs') as H'.
      { eapply elem_of_list_lookup_2.
        erewrite lookup_zip_Some. naive_solver.
      }
      iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
      simpl.
      iDestruct "H" as "[? [H ?]]".
      by iDestruct (ghost_map_lookup with "Htl2 H") as "%".
    }
    iAssert (⌜(∀ p, p ∈ zip_with (λ x y, (x.1.2,y.1.2)) ls ls' -> (dZ p.1 p.2 <= 1)%R)⌝)%I as "%".
    {
      iIntros ([z z'] H').
      rewrite elem_of_lookup_zip_with in H'.
      destruct H' as (k&[[]]&[[]]&?&K1 &K2); destruct!/=.
      rewrite big_sepL2_alt.
      rewrite /ls/ls' in K1, K2.
      repeat rewrite lookup_zip_Some in K1, K2.
      rewrite !list_lookup_fmap !lookup_replicate in K1, K2.
      destruct (xιs!!k) as [[]|] eqn:?; last naive_solver.
      destruct (xιs'!!k) as [[]|] eqn:?; last naive_solver.
      destruct!/=.
      iDestruct "Hlist" as "[_ Hlist]".
      eassert (_∈zip xιs xιs') as H'.
      { eapply elem_of_list_lookup_2.
        erewrite lookup_zip_Some. naive_solver.
      }
      iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
      simpl.
      by iDestruct "H" as "(?&?&%)".
    }
    iApply (spec_coupl_erasables_weak _ _ _ ε'' ε_now_rest _ 0%NNR δ) => //.
    - apply nnreal_ext. simpl. lra.
    - rewrite Hε''.
      apply laplace_state_list_coupl; [| | |done|..]; try done.
      + unfold ls. unfold ls'.
        rewrite !length_zip!length_replicate!length_fmap. lia.
      + unfold ls.
        rewrite !length_zip!length_replicate!length_fmap. lia.
      + unfold ls.
        rewrite fst_zip; last first.
        { rewrite !length_zip!length_replicate!length_fmap. lia. }
        rewrite fst_zip; first done.
        rewrite !length_fmap. lia.
      + unfold ls'.
        rewrite fst_zip; last first.
        { rewrite !length_zip!length_replicate!length_fmap. lia. }
        rewrite fst_zip; first done.
        rewrite !length_fmap. lia.
    - eapply laplace_presample_list_erasable; try done.
      unfold ls.
      rewrite !fst_zip; first done.
      + rewrite !length_fmap. lia.
      + rewrite !length_zip!length_replicate!length_fmap. lia.
    - eapply laplace_presample_list_erasable; try done.
      unfold ls.
      rewrite !fst_zip; first done.
      + rewrite !length_fmap. lia.
      + rewrite !length_zip!length_replicate!length_fmap. lia.
    - simpl.
      iIntros (σ2 σ2') "(%zs & %zs' &%Hlen4 &%Hlen5&%Hmax&%Hforall1&%Hforall2)".
      iMod (ecm_supply_decrease with "Hε2 Herr") as (????) "H".
      iApply spec_coupl_ret.
      iModIntro.
      subst.
      rewrite /spec_auth/=.
      simpl.
      unfold ls in *.
      rewrite !length_zip !length_fmap !length_replicate in Hlen5.
      destruct σ, σ'.
      rewrite !replace_laplace_tape_heap !replace_laplace_tape_tapes.
      iFrame. 
      iMod (hoare_couple_laplace_list_update _ _ zs zs' with "[$][$][$]") as "Hrest"; try done; try lia.
      iDestruct "Hrest" as "(?&?&?)".
      iFrame.
      iMod "Hclose'".
      iModIntro.
      iSplitL "H".
      + iApply ecm_supply_eq; last done. simplify_eq. lra.
      + iApply "HΦ".
        iFrame.
        repeat iSplit; iPureIntro; lia.
  Qed. 
  
End coupling_rule.
