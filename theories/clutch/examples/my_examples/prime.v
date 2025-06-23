From clutch Require Import clutch.
From clutch.prob_lang Require Import advantage.
From clutch.prob_lang.typing Require Import tychk.
From clutch.clutch.examples.crypto Require Import valgroup advantage_laws.
From clutch.clutch.examples.crypto Require ElGamal_bijection.

From mathcomp Require ssrnat.
From mathcomp Require Import zmodp finset ssrbool fingroup.fingroup solvable.cyclic.
Import valgroup_notation.
From clutch.clutch.examples.crypto Require Import ElGamal.

Set Default Proof Using "Type*".

Section Prime.

(* outputs `true` with probability (k/n)^i and `false otherwise` *)
Definition bernoulli : expr :=
  rec: "bernoulli" "k" "n" "i" :=
    if: "i" = #0 then #true
    else
      let: "r" := rand "n" in
      if: "k" ≤ "r" then
        #false
      else "bernoulli" "k" "n" ("i" - #1).

Definition bernoulli_tape : expr :=
  rec: "bernoulli" "k" "n" "i" :=
    let: "ι" := alloc "n" in
    if: "i" = #0 then #true
    else
      let: "r" := rand "n" "ι" in
      if: "k" ≤ "r" then #false
      else "bernoulli" "k" "n" ("i" - #1).

Fixpoint is_div_minus_two (n d : nat) := match n with
  | O => false
  | S n' => if (S n') =? (d+2) then true else is_div_minus_two (n' - (d+1)) d
end.

Definition proper_div : val :=
  rec: "is_div_minus_two" "n" "d'" :=
    if: "n" = #0 then #false
    else
      if: "n" = ("d'"+#2) then
        #true
      else
        "is_div_minus_two" ("n" - ("d'" + #2)) "d'"
.

Definition prime_proba_rec : expr :=
  rec: "prime_proba_rec" "n" "k_iter" :=
    if: "k_iter" = #0 then #true
    else
      let: "d" := rand ("n"-#2) in
      if: proper_div "d" "n" then #false
      else "prime_proba_rec" "n" ("k_iter" - #1).

Definition prime_proba : expr :=
  rec: "prime_proba" "n" "k_iter" :=
    if: "n" ≤ #1 then #false
    else if: "k_iter" < #0 then #false
      else prime_proba_rec "n" "k_iter".

Definition b2n : expr := λ: "b", if: "b" then #1 else #0.

Definition count_div_aux : val :=
  (rec: "count_div_aux" "n" "i":=
    if: "i" = #0 then
      b2n (proper_div "n" "i")
    else
      b2n (proper_div "n" "i") + "count_div_aux" "n" ("i" - #1)
  ).

Definition count_divisor : expr :=
  λ: "n",
  count_div_aux "n" ("n" - #2).

Definition prime_error : expr :=
  λ: "n" "k_iter",
    if: "n" ≤ #1 then #false
    else if: "k_iter" < #0 then #false
      else
        let: "nb_div" := count_divisor "n" in
        if: "nb_div" = #0 then #true
        else bernoulli "nb_div" ("n"-#2) "k_iter". 

Definition prime_error_tape : expr :=
  λ: "n" "k_iter",
    let: "nb_div" := count_divisor "n" in
    if: "nb_div" = #0 then
      #true
    else
      bernoulli_tape "nb_div" ("n"-#2) "k_iter". 

Definition τ := (TInt → TInt → TBool)%ty.

Section Logrel.

Fixpoint bij_aux (E : nat -> bool) (N : nat) (elem i : nat) := match i with
  | O => if 0 =? elem then (Nat.b2n (E 0), 0) else (Nat.b2n (E 0), Nat.b2n (E 0))
  | S i' => if S i' <? elem then
              (Nat.b2n (E (S i')) + fst (bij_aux E N elem i'),
               Nat.b2n (E (S i')) + snd (bij_aux E N elem i'))
            else
              (Nat.b2n (E (S i')) + fst (bij_aux E N elem i'),
                snd (bij_aux E N elem i'))
end.

Fixpoint count_E (E : nat -> bool) (N : nat) := match N with
  | O => Nat.b2n (E 0)
  | S N' => Nat.b2n (E (S N')) + (count_E E N')
end.

Lemma count_E_proj_bij : forall (E : nat -> bool) (N elem i : nat),
  fst (bij_aux E N elem i) = count_E E i.
Proof. induction i as [|i'].
  - simpl. destruct elem; done.
  - simpl. destruct (S i' <? elem); simpl; rewrite IHi'; done.
Qed.

Definition bij_pos (E : nat -> bool) (N : nat) (elem : nat) : nat * nat :=
  bij_aux E N elem N.

Definition bij_neg (E : nat -> bool) (N : nat) (elem : nat) : nat * nat :=
  bij_aux (fun n => negb (E n)) N elem N.

Definition bij_subset (E : nat -> bool) (N : nat) (elem : nat) : nat :=
  if E elem then
    snd (bij_pos E N elem)
  else
    (fst (bij_pos E N elem)) + (snd (bij_neg E N elem)).

Lemma bij_aux_ineq : forall (E : nat -> bool) (N elem i : nat),
  E elem = true ->
  (elem > i)  ∧ (snd (bij_aux E N elem i) = fst (bij_aux E N elem i)) ∨
  (elem <= i) ∧ (snd (bij_aux E N elem i) < fst (bij_aux E N elem i)).
Proof. intros *. induction i as [|i' IHi].
  - simpl. intro HE. destruct elem.
    + simpl. right. split; first constructor.
      rewrite HE; simpl; lia.
    + simpl. left. split; first lia.
      reflexivity.
  - simpl. intro HE. apply IHi in HE as H'.
    destruct H' as [[ineq IH]|[ineq IH]]; clear IHi.
    + destruct (PeanoNat.Nat.eq_dec (S i') elem).
      * subst. right. split; first lia.
        assert (H : S i' <? S i' = false). { apply Nat.ltb_ge; lia. } rewrite H; clear H.
        simpl. rewrite IH. rewrite HE; simpl; lia.
      * left. split; first lia. assert (S i' <? elem = true). {
          apply Nat.ltb_lt. lia.
        }
        rewrite H; clear H. simpl. rewrite IH; reflexivity.
    + right. split; first lia. assert (S i' <? elem = false). {
          apply Nat.ltb_ge. lia.
        }
        rewrite H; clear H. simpl. lia.
Qed.

Lemma completeness_pos_neg : forall (E : nat -> bool) (N elem i : nat),
  fst (bij_aux E N elem i) + fst (bij_aux (fun n => negb (E n)) N elem i) = S i.
Proof. intros E N elem i. induction i as [|i' IHi].
  - simpl. destruct elem as [|elem']; destruct (E 0); simpl; reflexivity.
  - simpl. destruct (S i' <? elem) eqn:ineq; destruct (E (S i')); simpl; lia.
Qed.

Lemma bij_subset_is_bij : forall (E : nat -> bool) (N elem : nat),
  elem <= N ->
  bij_subset E N elem ≤ N.
Proof.
  intros *. rewrite /bij_subset. rewrite /bij_pos. rewrite /bij_neg.
  destruct (E elem) eqn:eq.
  - apply (bij_aux_ineq E N elem N) in eq as H'.
    destruct H' as [[ineq Heq] | [ineq Heq]].
    + intro H. exfalso; lia.
    + intros _. apply PeanoNat.lt_n_Sm_le. eapply Nat.lt_le_trans; first apply Heq.
      pose proof (completeness_pos_neg E N elem N). lia.
  - pose proof (bij_aux_ineq (fun x => negb (E x)) N elem N) as H.
    assert (eq' : (fun x => negb (E x)) elem = true). { rewrite eq. reflexivity. }
    apply H in eq'. clear H. destruct eq' as [[ineq Heq] | [ineq Heq]].
    + intro H; exfalso; lia.
    + intros _. apply PeanoNat.lt_n_Sm_le. eapply Nat.lt_le_trans.
      * apply Nat.add_lt_mono_l. apply Heq.
      * rewrite completeness_pos_neg. constructor.
Qed.

Lemma bij_subset_fin_bij : forall (E : nat -> bool) (N : nat) (fin_e : fin (S N)),
  bij_subset E N (fin_to_nat fin_e) < S N.
Proof. intros *. apply PeanoNat.le_lt_n_Sm. apply bij_subset_is_bij.
  apply fin.fin_to_nat_le.
Qed. 

Definition bij_subset_div (N : nat) (n : fin (S (N - 2))) : fin (S (N-2)) :=
  nat_to_fin (bij_subset_fin_bij (is_div_minus_two N) (N - 2) n).

(* Actually proving logrel now *)
Context `{!clutchRGS Σ}.
Context {Δ : listO (lrelC Σ)}.

Definition T := Eval cbn in (interp τ Δ).

Lemma Z_is_of_nat : forall (n : nat), #(n+1)%Z = #(n+1)%nat.
Proof. intros n. induction n as [|n']; first done.
  simpl. assert ((S n' + 1)%Z = (S (n' + 1))%Z). { lia. } rewrite H. reflexivity.
Qed.

Lemma proper_div_spec : ∀ (n d : nat), ⊢ WP proper_div #n #d
  {{ v, ⌜v = #(is_div_minus_two n d)⌝ }}.
Proof. iLöb as "IH". iIntros (n d). iStartProof. destruct n as [|n'].
  - simpl. rewrite /proper_div. wp_pures. done.
  - simpl. rewrite /proper_div. wp_pure. wp_pure. wp_pure. wp_pure.
    wp_pure.
    destruct (S n' =? d+2) eqn:eq.
    + wp_pures. assert (Heq : bool_decide (#(S n') = #(d + 2)) = true). {
        admit.
      }
      rewrite Heq. wp_pures. iModIntro; iPureIntro.
      simpl in eq. rewrite eq. reflexivity.
    + wp_pures. assert (Heq : bool_decide (#(S n') = #(d + 2)) = false). { admit. }
      rewrite Heq. simpl in eq. rewrite eq.
      wp_if_false. clear eq Heq. assert (n' - (d+1) = S n' - (d + 2)).
      { lia. } rewrite H. simpl.
      remember (S n' - (d+2)) as n eqn:Heqn.
      assert (eq : (#(S n') - (#d + #2))%E = #n).
      { simpl. rewrite -H. admit. } rewrite eq. fold proper_div. wp_apply "IH".
Admitted.

Lemma b2n_spec : forall (b : bool),
  ⊢ WP if: #b then #1 else #0 {{ v, ⌜v = #(Nat.b2n b)⌝ }}.
Proof. destruct b as [|]; simpl; wp_pures; iModIntro; iPureIntro; done. Qed.


Lemma count_div_aux_spec : ∀ (n i : nat),
  ⊢ WP count_div_aux #n #i
    {{ v, ⌜v = #(count_E (is_div_minus_two n) i)⌝ }}.
Proof. iLöb as "IH". iIntros (n i).
  rewrite /count_div_aux.
  destruct (bool_decide (#i = #0)) eqn:H.
  - wp_pures. rewrite H. wp_if_true. assert (#i = #0) as eqi.
    { admit. } rewrite eqi. injection eqi. intro eqiZ'.
    assert (eqiZ : i = 0). { lia. }
    clear eqiZ'. subst. simpl. iClear "IH".
    wp_bind (proper_div _ _).
    wp_apply (wp_mono _ _  (fun v => ⌜v = #(is_div_minus_two n 0)⌝)%I).
    + simpl. clear H eqi. iIntros (v H). subst. simpl. wp_let.
      wp_apply b2n_spec.
    + wp_apply (proper_div_spec n 0).
  - wp_pures. rewrite H. wp_if_false.
wp_pure. Admitted.


Lemma count_divisor_spec : ∀ (n : nat), ⌜ 2 <= n ⌝ ⊢ WP count_divisor #n
  {{ v, ⌜v = #(count_E (is_div_minus_two n) (n-2))⌝ }}.
Proof. iIntros (n) "%H". rewrite /count_divisor. 
  wp_let. wp_pure.
  assert ((n-2)%Z = (n-2)%nat). { lia. } rewrite H0. wp_apply count_div_aux_spec.
Qed.

Lemma rel_cont_r : ∀ (e e_left : expr) (K : ectx_item) (v' : val) (T : lrel Σ), ⊢
  WP e {{ v, ⌜ v = v' ⌝ }} -∗ refines top e_left (fill [K] v') T -∗
  refines top e_left (fill [K] e) T.
Proof. Admitted.

Lemma rel_cont_l : ∀ (e e_right : expr) (K : ectx_item) (v' : val) (T : lrel Σ),
  ⊢ WP e {{ v, ⌜ v = v' ⌝ }} -∗ refines top (fill [K] v') e_right T -∗
  refines top (fill [K] e) e_right T.
Proof. Admitted.

Definition prog_test : val :=
  rec: "f" "x" := let: "y" := ("x" + #1) in "f" "x".

Lemma test : ∀ (n: nat), ⊢ WP prog_test #n {{ v, True }}.
Proof.
  iIntros (n). iLöb as "IH". rewrite /prog_test. wp_pure. wp_pure. wp_pure.
  wp_pure. fold prog_test. wp_apply "IH".
Qed.

Lemma prime_proba_bernoulli : ⊢ refines top prime_proba prime_error T.
Proof. rewrite /prime_proba. rewrite /prime_error.
  rel_pures_r. rel_arrow_val.
  iIntros (v1 v2) "%H". destruct H as [n [eq1 eq2]]. subst.
  rel_arrow_val. iIntros (v1 v2) "%H". destruct H as [k_iter [eq1 eq2]]; subst.
  rel_rec_r.
  destruct n as [ | n | n]; try (rel_pures_l; rel_pures_r; rel_values).
  rewrite -positive_nat_Z. remember (Pos.to_nat n) as N eqn:eqN.
  clear eqN. clear n. destruct (le_le_S_dec N 1).
  - rel_pures_l. rel_pures_r. assert (H : bool_decide (N ≤ 1)%Z = true).
    { pose proof (bool_decide_reflect (N ≤ 1)%Z). inversion H; lia. }
    rewrite H. rel_pures_r; rel_pures_l. rel_values.
  - assert (H : bool_decide (N ≤ 1)%Z = false).
    { pose proof (bool_decide_reflect (N ≤ 1)%Z). inversion H; lia. }
    rel_pures_l; rel_pures_r. rewrite H. clear H. rel_if_r; rel_if_l.
    destruct k_iter as [ | k_iter | k_iter]; try (rel_pures_l; rel_pures_r; rel_values).
    {
      rel_pures_l. rel_pure_r. rel_pure_r.
      fold count_divisor. rel_bind_r (count_divisor _)%E.
      rel_apply rel_cont_r.
      + iPoseProof (count_divisor_spec N) as "H'".
        iApply "H'". iPureIntro. assumption.
      + rel_pures_r. 
        destruct (count_E (is_div_minus_two N) (N - 2)) as [| n_div'] eqn:eqdiv;
        rel_pures_r; rel_values.
    }
    rewrite -positive_nat_Z. remember (Pos.to_nat k_iter) as K eqn:eqK.
    clear eqK. clear k_iter. assert (bool_decide (K < 0)%Z = false).
    { pose proof (bool_decide_reflect (K < 0)%Z). inversion H as [H0 H1 | H0 H1]; lia. }
    rel_pure_l; rel_pure_r. rewrite H. rel_if_r; rel_if_l.
    fold count_divisor. rel_bind_r (count_divisor _)%E.
    rel_apply rel_cont_r.
    + iPoseProof (count_divisor_spec N) as "H'".
      iApply "H'". iPureIntro. assumption.
    + rel_pures_r. fold bernoulli.
      destruct (count_E (is_div_minus_two N) (N - 2)) as [| n_div'] eqn:eqdiv.
      * rel_pures_r. admit.
      * rel_pure_r. rewrite -eqdiv.
        iLöb as "IH". clear H.
        { destruct K as [|K'].
        - rel_pures_l. rel_pures_r. rel_values.
        - rel_pures_l. rel_pures_r.
          rel_couple_UU. remember (bij_subset_div (Z.to_nat N)) as f.
          assert (eqtype : Z.to_nat N - 2 = Z.to_nat (N-2)).
          { lia. } admit. }
Admitted.

End Logrel.

End Prime.