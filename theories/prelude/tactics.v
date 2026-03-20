From clutch.prelude Require Import base.
From stdpp Require Export prelude gmap strings pretty.
From iris.prelude Require Export prelude.
From iris.proofmode Require Import proofmode.


Set Default Proof Using "Type*".

(** * Tactics from Dimsum 
    https://gitlab.mpi-sws.org/iris/dimsum/-/tree/master?ref_type=heads
*)
(** 
    - inv_all
    - case_bool_decide (_)
    - econs 
    - destruct!
    - split!
    - simplify_map_eq'
    - sort_map_insert
    - simpl_map_decide
    - iDestruct!
    - iIntros!
    - iSplit!
 *)

(** Inspired by inv in CompCert/Coqlib.v *)
(* TODO: upstream? See https://gitlab.mpi-sws.org/iris/stdpp/-/issues/40 *)
Tactic Notation "inv/=" ident(H) := inversion H; clear H; simplify_eq/=.

Ltac inv_all_tac f :=
  repeat lazymatch goal with
         | H : f |- _ => inv H
         | H : f _ |- _ => inv H
         | H : f _ _|- _ => inv H
         | H : f _ _ _|- _ => inv H
         | H : f _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _ _ _|- _ => inv H
         | H : f _ _ _ _ _ _ _ _ _|- _ => inv H
         end.

Tactic Notation "inv_all/=" constr(f) := inv_all_tac f; simplify_eq/=.
Tactic Notation "inv_all" constr(f) := inv_all_tac f.

Tactic Notation "case_bool_decide" open_constr(pat) "as" ident(Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    unify P pat;
    destruct_decide (@bool_decide_reflect P dec) as Hd
  | |- context [@bool_decide ?P ?dec] =>
    unify P pat;
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.
Tactic Notation "case_bool_decide" open_constr(pat) :=
  let H := fresh in case_bool_decide pat as H.

(** abbreviations for [econstructor] *)
Tactic Notation "econs" := econstructor.
Tactic Notation "econs" integer(n) := econstructor n.

(** [fast_set_solver] is a faster version of [set_solver] that does
not call set_unfold and setoid_subst so often. *)
(* TODO: figure out why this is necessary *)
Ltac fast_set_solver := set_unfold; naive_solver.



(** [destruct!] destructs things in the context *)
Ltac destruct_go tac :=
  repeat match goal with
         | H : context [ match ?x with | (y, z) => _ end] |- _ =>
             let y := fresh y in
             let z := fresh z in
             destruct x as [y z]
         | H : ∃ x, _ |- _ => let x := fresh x in destruct H as [x H]
         | |- _ => destruct_and!
         | |- _ => destruct_or!
         | |- _ => progress simplify_eq
         | |- _ => tac
         end.

Tactic Notation "destruct!" := destruct_go ltac:(fail).
Tactic Notation "destruct!/=" := destruct_go ltac:( progress csimpl in * ).

(** [split_or] tries to simplify an or in the goal by proving that one side implies False. *)
Ltac split_or :=
  repeat match goal with
         | |- ?P ∨ _ =>
             assert_succeeds (exfalso; assert P; [|
               destruct!;
               repeat match goal with | H : ?Q |- _ => has_evar Q; clear H end;
               done]);
             right
         | |- _ ∨ ?P =>
             assert_succeeds (exfalso; assert P; [|
               destruct!;
               repeat match goal with | H : ?Q |- _ => has_evar Q; clear H end;
               done]);
             left
         end.



(** [SplitAssumeInj] *)
Class SplitAssumeInj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop := split_assume_inj : True.
Global Instance split_assume_inj_inj A B R S (f : A → B) `{!Inj R S f} : SplitAssumeInj R S f.
Proof. done. Qed.

Class SplitAssumeInj2 {A B C} (R1 : relation A) (R2 : relation B) (S : relation C) (f : A → B → C) : Prop := split_assume_inj2 : True.
Global Instance split_assume_inj2_inj2 A B C R1 R2 S (f : A → B → C) `{!Inj2 R1 R2 S f} : SplitAssumeInj2 R1 R2 S f.
Proof. done. Qed.

(** [split!] splits the goal *)
Ltac split_step tac :=
  match goal with
  | |- ∃ x, _ => eexists _
  | |- _ ∧ _ => split
  | |- _ ∨ _ => split_or
  | |- True → _ => intros _
  (* | |- ?P → ?Q => *)
   (* lazymatch type of P with *)
   (* TODO: replace this with assert_is_trivial from RefinedC? *)
   (* | Prop => assert_succeeds (assert (P) as _;[fast_done|]); intros _ *)
   (* end *)
  | |- ?e1 = ?e2 => is_evar e1; reflexivity
  | |- ?e1 = ?e2 => is_evar e2; reflexivity
  | |- ?e1 ≡ ?e2 => is_evar e1; reflexivity
  | |- ?e1 ≡ ?e2 => is_evar e2; reflexivity
  | |- ?G => assert_fails (has_evar G); done
  | H : ?o = Some ?x |- ?o = Some ?y => assert (x = y); [|congruence]
  | |- ?x = ?y  =>
      (* simplify goals where the head are constructors, like
         EICall f vs h = EICall ?Goal7 ?Goal8 ?Goal9 *)
      once (first [ has_evar x | has_evar y]);
      let hx := get_head x in
      is_constructor hx;
      let hy := get_head y in
      match hx with
      | hy => idtac
      end;
      apply f_equal_help
  | |- ?f ?a1 ?a2 = ?f ?b1 ?b2 =>
      let _ := constr:(_ : SplitAssumeInj2 (=) (=) (=) f) in
      apply f_equal_help; [apply f_equal_help; [done|]|]
  | |- ?f ?a = ?f ?b =>
      let _ := constr:(_ : SplitAssumeInj (=) (=) f) in
      apply f_equal_help; [done|]
  | |- _ => tac
  end; simpl.

Ltac split_tac tac :=
  (* The outer repeat is because later split_steps may have
  instantiated evars and thus we try earlier goals again. *)
  repeat (simpl; repeat split_step tac).

Tactic Notation "split!" := split_tac ltac:(fail).


(** [simplify_map_eq'] is a version of [simplify_map_eq] that also simplifies lookup total. *)
Tactic Notation "simpl_map_total" "by" tactic3(tac) := repeat
   match goal with
   | H : ?m !! ?i = Some ?x |- context [?m !!! ?i] =>
       rewrite (lookup_total_correct m i x H)
   | H1 : context [?m !!! ?i], H2 : ?m !! ?i = Some ?x |- _ =>
      rewrite (lookup_total_correct m i x H2) in H1
   | |- context [<[ ?i := ?x ]> (<[ ?i := ?y ]> ?m)] =>
       rewrite (insert_insert m i x y)
   | |- context[ (<[_:=_]>_) !!! _ ] =>
       rewrite lookup_total_insert || rewrite ->lookup_total_insert_ne by tac
   | H : context[ (<[_:=_]>_) !!! _ ] |- _ =>
       rewrite lookup_total_insert in H || rewrite ->lookup_total_insert_ne in H by tac
   | H : ?m !!! ?i = ?x |- context [?m !!! ?i] =>
       rewrite H
   | H : ?x = ?m !!! ?i |- context [?m !!! ?i] =>
       is_closed_term x; rewrite -H
   | H1 : ?m !!! ?i = ?x, H2 : context [?m !!! ?i] |- _ =>
       rewrite H1 in H2
   | H1 : ?x = ?m !!! ?i, H2 : context [?m !!! ?i] |- _ =>
       is_closed_term x; rewrite -H1 in H2
   (* | H : ?m !!! ?i = ?m2 !!! ?i2 |- context [?m !!! ?i] => *)
   (*     rewrite H *)
   (* | H1 : ?m !!! ?i = ?m2 !!! ?i2, H2 : context [?m !!! ?i] |- _ => *)
   (*     rewrite H1 in H2 *)
   end.
 Tactic Notation "simplify_map_eq'" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || (progress simpl_map_total by tac) || simplify_map_eq by tac ).
 Tactic Notation "simplify_map_eq'" :=
  repeat (progress (simpl_map_total by eauto with simpl_map map_disjoint) || simplify_map_eq by eauto with simpl_map map_disjoint ).
Tactic Notation "simplify_map_eq'" "/=" :=
  simplify_map_eq'/= by eauto with simpl_map map_disjoint.

(** [sort_map_insert] sorts concrete inserts such that they can later be eliminated via [insert_insert]. *)
Ltac sort_map_insert :=
  repeat match goal with
         | |- context [<[ ?i := ?x ]> (<[ ?j := ?y ]> ?m)] =>
             is_closed_term i;
             is_closed_term j;
             assert_succeeds (assert (encode j <? encode i)%positive; [vm_compute; exact I|]);
             rewrite (insert_commute m i j x y); [|done]
         end.

(** [simpl_map_decide] tries to simplify bool_decide in the goal *)
(* TODO: make more principled *)
Ltac simpl_map_decide :=
  let go' := first [done | by apply elem_of_dom | by apply not_elem_of_dom] in
  let go := solve [ first [go' | by match goal with | H : _ ## _ |- _ => move => ?; apply: H; go' end] ] in
  repeat (match goal with
  | |- context [bool_decide (?P)] => rewrite (bool_decide_true P); [|go]
  | |- context [bool_decide (?P)] => rewrite (bool_decide_false P); [|go]
  end; simpl).

(** ** [iDestruct!] *)
Tactic Notation "iDestruct!" :=
  repeat (
     iMatchHyp (fun H P =>
        match P with
        | False%I => iDestruct H as %[]
        | True%I => iDestruct H as %(_)
        | emp%I => iDestruct H as "_"
        | ⌜_⌝%I => iDestruct H as %?
        | (_ ∗ _)%I => iDestruct H as "[??]"
        | (∃ x, _)%I => iDestruct H as (?) "?"
        | (□ _)%I => iDestruct H as "#?"
        | (_ ∨ _)%I => iDestruct H as "[?|?]"
        end)
  || simplify_eq/=).

Tactic Notation "iIntros!" := iIntros; iDestruct!.

(** ** [iSplit!] *)
Ltac iSplit_step tac :=
  lazymatch goal with
  | |- environments.envs_entails _ (∃ x, _)%I => iExists _
  | |- environments.envs_entails _ (_ ∗ _)%I => iSplit
  | |- environments.envs_entails _ (⌜_⌝)%I => iPureIntro
  | |- _ => split_step tac
  end; simpl.

Ltac iSplit_tac tac :=
  (* The outer repeat is because later split_steps may have
  instantiated evars and thus we try earlier goals again. *)
  repeat (simpl; repeat iSplit_step tac).

Tactic Notation "iSplit!" := iSplit_tac ltac:(fail).

Ltac andb_solver :=
  repeat match goal with
  | H : ?b1 && ?b2 = true |- _ =>
      apply andb_true_iff in H; destruct H as [? ?]
    | |- context [_ && _ =true] =>
        rewrite andb_true_iff
  end.
