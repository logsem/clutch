From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling Require Import bernoulli.

Section Tape.
  #[local] Open Scope fin.

  Fixpoint is_geometric_translation (b : list (fin 2)) (g : list nat) := 
    match g with
    | [] => b = []
    | n::g =>
        ∃ suf, 
        b = (repeat 0 n ++ [1]) ++ suf ∧
        is_geometric_translation suf g
    end.

  Fixpoint bernoulli_to_geometric_aux (l : list (fin 2)) (acc : nat) : list nat := 
    match l with 
    | 0::l => bernoulli_to_geometric_aux l (S acc)
    | 1::l => acc :: bernoulli_to_geometric_aux l 0
    | _ => []
    end.

  
    
  Definition bernoulli_to_geometric v := bernoulli_to_geometric_aux v 0.

  Fixpoint geometric_to_bernoulli (g : list nat) : list (fin 2) :=
    match g with 
    | [] => []
    | h::g => repeat 0 h ++ [1] ++ geometric_to_bernoulli g
    end.

  Lemma bernoulli_to_geometric_aux_repeat_0 (n acc : nat) :
    bernoulli_to_geometric_aux (repeat 0 n) acc = [].
  Proof.
    elim: n acc => /= [|n IH] acc //.
  Qed. 
  Lemma bernoulli_to_geometric_repeat_0 (n : nat) :
    bernoulli_to_geometric (repeat 0 n) = [].
  Proof.
    apply bernoulli_to_geometric_aux_repeat_0.
  Qed.
  
  Lemma bernoulli_to_geometric_aux_repeat (n acc : nat) :
    bernoulli_to_geometric_aux (repeat 0 n ++ [1]) acc = [n + acc].
  Proof.
    elim: n acc => /= [|n IH] acc //.
    rewrite /bernoulli_to_geometric /= IH.
    f_equal; lia.
  Qed. 
  Lemma bernoulli_to_geometric_repeat (n : nat) :
    bernoulli_to_geometric (repeat 0 n ++ [1]) = [n].
  Proof.
    rewrite /bernoulli_to_geometric bernoulli_to_geometric_aux_repeat.
    f_equal; lia.
  Qed.

  Lemma bernoulli_to_geometric_aux_app (l1 l2 : list (fin 2)) (acc : nat) :
    bernoulli_to_geometric_aux (l1 ++ [1] ++ l2) acc = bernoulli_to_geometric_aux (l1 ++ [1]) acc ++ bernoulli_to_geometric l2.
  Proof.
    elim: l1 acc => /= [|h1 t1 IH] acc //.
    rewrite !IH //.
    by full_inv_fin.
  Qed.

  Lemma bernoulli_to_geometric_app (l1 l2 : list (fin 2)) :
    bernoulli_to_geometric (l1 ++ [1] ++ l2) = bernoulli_to_geometric (l1 ++ [1]) ++ bernoulli_to_geometric l2.
  Proof.
    apply bernoulli_to_geometric_aux_app.
  Qed.

  Lemma geometric_to_bernoulli_to_geometric (g : list nat) :
    (bernoulli_to_geometric ∘ geometric_to_bernoulli) g = g.
  Proof.
    elim: g => /= [|h g IH] //.
    rewrite bernoulli_to_geometric_app IH bernoulli_to_geometric_repeat.
    reflexivity.
  Qed.

  Lemma list_decomposition (l : list (fin 2)) :
    { '(ns, n) | l = (flat_map (fun v => repeat 0 v ++ [1]) ns) ++ repeat 0 n }.
  Proof.
    elim: l => [|h t [[ns n] ->]]; first (by exists ([], 0%nat));
    full_inv_fin; first case ns => [|hns tns];
    by 
      [ exists ([], (S n))
      | exists ((S hns :: tns), n)
      | exists ((0%nat :: ns), n) ].
  Qed.

  Lemma bernoulli_to_geometric_to_bernoulli (b : list (fin 2)) :
    (geometric_to_bernoulli ∘ bernoulli_to_geometric) (b ++ [1]) = b ++ [1].
  Proof.
    case: (list_decomposition b) => [[ns n] ->].
    elim: ns => [|hns tns IHns] /=; first rewrite bernoulli_to_geometric_repeat //.
    rewrite -!app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat /=.
    do 2 f_equal.
    simpl in IHns.
    rewrite !app_assoc IHns //.
  Qed.
  
  Lemma bernoulli_to_geometric_translation (v : list (fin 2)) (l : list nat) :
    is_geometric_translation v l ↔ l = bernoulli_to_geometric v ∧ ∀ l' k, v = l' ++ [k] -> k = 1.
  Proof.
    elim: l v => [|h l IH] v //=; split.
    - move=> ->. split=>[|[|??] ? ?] //.
    - destruct v as [| e v ] using rev_ind.
      + split=>[|[|??] ? ?] //.
      + move=>[H1 H2].
        rewrite (H2 v e eq_refl) in H1.
        case: (list_decomposition v) => [[ns n] Heq].
        rewrite Heq in H1.
        destruct ns; simpl in H1.
        * rewrite bernoulli_to_geometric_repeat // in H1.
        * rewrite -!app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat // in H1.
    - intros (suf & Hv_eq & Htranslation_suf).
      subst v.
      split.
      + rewrite -app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat.
        f_equal.
        by apply IH.
      + move=> l' k Heq.
        destruct suf as [| e suf _] using rev_ind.
        * rewrite app_nil_r in Heq.
          by apply list_snoc_singleton_inv in Heq as [_ ->].
        * apply IH in Htranslation_suf as [_ Heqsuf].
          apply (Heqsuf suf). 
          rewrite app_assoc in Heq.
          by apply list_snoc_singleton_inv in Heq as [_ ->].
  - move => [Heq Hend1].
    case: (list_decomposition v) => [[ns n] Heqv]. subst v.
    assert (n = 0%nat) as ->.
    { destruct n as [|n]; first done.
      specialize Hend1 with (flat_map (λ v : nat, repeat 0 v ++ [1]) ns ++ repeat 0 (n)) 0.
      exfalso.
      assert ((0 : fin 2) ≠ 1) as contra by by intro.
      apply contra, Hend1.
      replace (S n) with (n + 1)%nat by lia.
      rewrite repeat_app app_assoc //. }
    simpl in *.
    rewrite ->app_nil_r in *.
    destruct ns as [|n ns]; first done.
    simpl.
    rewrite /= -app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat in Heq.
    injection Heq as -> ->.
    eexists.
    split; first done.
    apply IH. split; first done.
    intros l' k Heq.
    apply Hend1 with (l' := (repeat 0 n ++ [1]) ++ l').
    rewrite /= Heq app_assoc //.
  Qed.




End Tape.
#[local] Open Scope R.


Section Geometric.
  #[local] Ltac done ::= 
    solve[lia || lra || nra || real_solver || tactics.done || auto].

  Context `{!erisGS Σ}.
  Definition geometric : val :=
    rec: "geometric" "N" "M" :=
    if: bernoulli "N" "M" = #1 then #0 else 
    #1 + "geometric" "N" "M"
  .
  
  Lemma geometric_spec (N M k : nat) (Hlt : (N <= M)%nat) (p := N / (S M)) :
  [[{↯ (1 - (((1 - p)^k) * p))%R }]]
    geometric #N #M
  [[{RET #k; True}]].
  Proof.
    assert (0 <= p <= 1)%R as Hp. {
      split; subst p; simpl_expr.
    }
    induction k.
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric Rmult_1_l.
      wp_pures.
      wp_apply (bernoulli_success_spec_simple with "Herr") as "%v ->".
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric.
      wp_pures.
      fold geometric.
      replace (1 - (1 - p)^(S k) * p) with ((1 - p) * (1 - (1 - p)^k * p) + p) by rewrite //=.
      wp_apply (twp_bernoulli_scale _ _ _ (1 - (1 - p) ^ k * p) 1 with "Herr") as "%n [[-> Herr] | [-> Herr]]";
      fold p; try done; last solve[cred_contra].
      { apply error_credits.Rle_0_le_minus.
        assert (0 <= ((1 - p) ^ k) <= 1)%R by (apply Rpow_le_1; lra).
        by apply Rmult_le_1. }
      wp_pures.
      wp_apply (IHk with "Herr") as "_".
      wp_pures.
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      by iApply "HΦ".
  Qed.


  (* 


  
  *)
End Geometric.
