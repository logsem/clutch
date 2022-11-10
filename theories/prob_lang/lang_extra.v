From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps.
From iris.algebra Require Export ofe.
From self.prob Require Import distribution.
From self.program_logic Require Export language ectx_language ectxi_language.
From self.prob_lang Require Export lang locations.
From iris.prelude Require Import options.
From self.prelude Require Import stdpp_ext.

Section rewriting_lemmas.

(* Rewriting lemmas for head_step and state_step *)

Context `{Countable A}.
Implicit Types h : (expr * state) -> distr A.
Lemma dbind_head_step_rec f x e σ h :
      dbind h (head_step (Rec f x e) σ) = h (Val (RecV f x e), σ) .
Admitted.


Lemma dbind_head_step_pair v1 v2 σ h :
  dbind h (head_step (Pair v1 v2) σ) =
             match v1, v2 with
               | Val v1', Val v2' => h (Val (PairV v1' v2'), σ)
               | _,_ => dzero
             end.
Admitted.

(*Lemma dbind_head_step_pair v1 v2 σ h:
  dbind h (head_step (Pair (Val v1) (Val v2)) σ) = h (Val (PairV v1 v2), σ).
Admitted.*)

Lemma dbind_head_step_injl v v' σ h:
  dbind h (head_step (InjL (Val v)) σ) = h (Val (InjLV v'), σ).
Admitted.

Lemma dbind_head_step_injr v v' σ h:
  dbind h (head_step (InjR (Val v)) σ) = h (Val (InjRV v'), σ).
Admitted.

Lemma dbind_head_step_app f x e1 v2 σ h:
  dbind h (head_step (App (Val (RecV f x e1)) (Val v2)) σ) = h (subst' x v2 (subst' f (RecV f x e1) e1), σ).
Admitted.

Lemma dbind_head_step_unop op v σ h:
  dbind h (head_step (UnOp op (Val v)) σ) = match un_op_eval op v with
                                              | Some v' => h (Val v', σ)
                                              | None => dzero
                                            end.
Admitted.


Lemma dbind_head_step_binop op v1 v2 σ h:
  dbind h (head_step (BinOp op (Val v1) (Val v2)) σ) = match bin_op_eval op v1 v2 with
                                                       | Some v' => h (Val v', σ)
                                                       | None => dzero
                                                       end.
Admitted.

Lemma dbind_head_step_ifT e1 e2 σ h:
  dbind h (head_step (If (Val (LitV (LitBool true))) e1 e2) σ) = h (e1 , σ).
Admitted.

Lemma dbind_head_step_ifF e1 e2 σ h:
  dbind h (head_step (If (Val (LitV (LitBool true))) e1 e2) σ) = h (e2 , σ).
Admitted.

Lemma dbind_head_step_fst v1 v2 σ h:
 dbind h (head_step (Fst (Val (PairV v1 v2))) σ) = h (Val v1, σ).
Admitted.

Lemma dbind_head_step_snd v1 v2 σ h:
 dbind h (head_step (Snd (Val (PairV v1 v2))) σ) = h (Val v2, σ).
Admitted.

Lemma dbind_head_step_caseL v e1 e2 σ h:
 dbind h (head_step (Case (Val (InjLV v)) e1 e2) σ) = h (e1 , σ).
Admitted.

Lemma dbind_head_step_caseR v e1 e2 σ h:
 dbind h (head_step (Case (Val (InjRV v)) e1 e2) σ) = h (e2 , σ).
Admitted.

Lemma dbind_head_step_alloc v σ h :
  dbind h (head_step (Alloc (Val v)) σ) =
      let ℓ := fresh_loc σ.(heap) in
      h (Val (LitV (LitLoc ℓ)), state_upd_heap <[ℓ:=v]> σ).
Admitted.

Lemma dbind_head_step_load l σ h :
  dbind h (head_step (Load (Val (LitV (LitLoc l)))) σ) =
    match (σ.(heap) !! l) with
      | Some v => h (Val v , σ)
      | None => dzero
    end.
Admitted.

Lemma dbind_head_step_store l w σ h :
  dbind h (head_step (Store (Val (LitV (LitLoc l))) (Val w)) σ) =
    match (σ.(heap) !! l) with
      | Some _ => h (Val (LitV LitUnit) , state_upd_heap <[l:=w]> σ)
      | None => dzero
    end.
Admitted.

Lemma dbind_head_step_alloc_tape v σ h :
  dbind h (head_step (Alloc (Val v)) σ) =
      let ℓ := fresh_loc σ.(heap) in
      h (Val (LitV (LitLbl ℓ)), state_upd_tapes <[ℓ:=[]]> σ).
Admitted.


Lemma dbind_state_step (σ : state) (α : loc) (h : state → distr A) :
  dbind h (state_step σ α) =
  fair_conv_comb
  (h (state_upd_tapes (<[α := σ.(tapes) !!! α ++ [true]]>) σ ))
  (h (state_upd_tapes (<[α := σ.(tapes) !!! α ++ [false]]>) σ)).
Admitted.

Lemma foo (σ σ': state) (e e' : expr) :
  (¬ (exists e'', e = Flip e'')) -> (head_step e σ (e', σ')) = 1%R \/ (head_step e σ (e', σ')) = 0%R.
Proof.
Admitted.

End rewriting_lemmas.


Section lang_properties.

Lemma state_after_prim (e1 : expr) (σ1 : state) (α : loc)  :
    (¬ (exists e', e1 = Flip e')) -> dbind (λ σ2, head_step e1 σ2) (state_step σ1 α) =
                                dbind (λ ρ, dbind (λ σ3 , dret (ρ.1, σ3))  (state_step ρ.2 α)) (head_step e1 σ1).
Proof.
 intro Hneq.
 rewrite dbind_state_step.
 apply distr_ext.
 intros (e3 & σ3).
 rewrite fair_conv_comb_pmf.
 assert ((λ ρ : cfg,
            dbind (λ σ0 : state, dret (ρ.1, σ0)) (state_step ρ.2 α)) =
         (λ ρ : cfg, fair_conv_comb (dret (ρ.1, (state_upd_tapes (<[α := ρ.2.(tapes) !!! α ++ [true]]>) ρ.2 )))
                          (dret (ρ.1, (state_upd_tapes (<[α := ρ.2.(tapes) !!! α ++ [false]]>) ρ.2 ))))) as Heq.
 { admit. }
 rewrite Heq.
 rewrite dbind_fair_conv_comb.
 rewrite fair_conv_comb_pmf.
 do 2 rewrite <- Rmult_plus_distr_l.
 apply Rmult_eq_compat_l.
 destruct e1 ; simpl.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + do 2 rewrite dbind_head_step_pair.
   rewrite {1 2}/pmf /= /head_step_pmf/=.
   destruct e1_1; destruct e1_2;simpl; try (rewrite /pmf /=; lra).
   rewrite /pmf /= /dret_pmf /=.
   destruct e3 eqn:He3; simpl; try lra.
   case_bool_decide; case_bool_decide.
   ++ simplify_eq.
      eapply insert_inv in H.
      simplify_map_eq.
   ++ simplify_eq.
      rewrite {1}bool_decide_eq_true_2; auto.
      rewrite bool_decide_eq_false_2; auto.
      rewrite /state_upd_tapes /=.
      intros (? & ? & [= ?%insert_inv]).
      simplify_map_eq.
   ++ inversion H0.
      rewrite bool_decide_eq_false_2; [ | admit ].
      rewrite bool_decide_eq_true_2; auto.
 +

   destruct (decide (e3 = Val(PairV v v0))) eqn:He3.
   ++ rewrite He3. destruct H. as (He3 & Hσ3).
 + admit.


 rewrite {3 4}/pmf /=/ dbind_pmf/=.
 rewrite {3 5}/pmf /= /head_step_pmf/=.
 destruct e1; simpl; auto.
 + simpl.
   destruct e; auto.
 
 rewrite {1}/pmf.  /=.
 setoid_rewrite (dbind_state_step).

 rewrite /pmf /= /dbind_pmf /=.
 setoid_rewrite bar.
 rewrite SeriesC_double_prod_rl.
 rewrite {4}/pmf /= /dbind_pmf /=.
 assert
   (SeriesC (λ b : state, SeriesC (λ a : expr, head_step e1 σ1 (a, b) * SeriesC (λ a0 : state, state_step b α a0 * dret (a, a0) (e3, σ3))))
   = SeriesC (λ b : state, SeriesC (λ a0 : state,  state_step b α a0 * SeriesC (λ a : expr, head_step e1 σ1 (a, b) * dret (a, a0) (e3, σ3))))) as Has.
 { admit.}
 rewrite Has.
 setoid_rewrite bar.
 rewrite {1 2 3}/pmf /= /dbind_pmf /=; destruct e1; simpl;
 try setoid_rewrite Rmult_0_r; try setoid_rewrite Rmult_0_l.
 + admit.
 + admit.
 + 

 rewrite /pmf /= /dret_pmf /= /state_step_pmf /= /strength_l /= /dmap /=.
 destruct e1; simpl; try setoid_rewrite Rmult_0_r; try setoid_rewrite Rmult_0_l;
   rewrite /head_step_pmf /=.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.
 + admit.


 /state_step_pmf /=.
 rewrite {3}/pmf /=. /state_step_pmf.
 rewrite SeriesC_double_prod_rl.
 apply SeriesC_ext.
 intro σ'.
 erewrite SeriesC_ext; [ rewrite -> SeriesC_singleton; reflexivity | ]; simpl.
 intro e2; simpl.
 destruct (foo σ σ' e e2 ) as [Heq | Heq]; auto; rewrite Heq.
 + destruct σ'.
   rewrite /state_step /state_step_pmf /=.
   ++ rewrite H.

   destruct (foo σ σ' e e2); auto.
   ++ rewrite H; simpl.
 +


 destruct (foo σ σ'').
 destruct e.
 + rewrite {2 3}/pmf /=.
   rewrite Rmult_0_r.
   setoid_rewrite Rmult_0_l.
   rewrite SeriesC_0; auto.
 + rewrite {2 3}/pmf /=.
   rewrite Rmult_0_r.
   setoid_rewrite Rmult_0_l.
   rewrite SeriesC_0; auto.
 + rewrite {2 3}/pmf /=.
   destruct e''.
   rewrite Rmult_0_r.
   setoid_rewrite Rmult_0_l.
   rewrite SeriesC_0; auto.

End lang_properties.
