From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.

Section Tape.
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli balloc}.
  
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

  Definition geometric_to_bernoulli : list nat -> list (fin 2) :=
    List.flat_map (fun h => repeat 0 h ++ [1]).

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
    bernoulli_to_geometric_aux (l1 ++ [1] ++ l2) acc 
      = 
    bernoulli_to_geometric_aux (l1 ++ [1]) acc ++ bernoulli_to_geometric l2.
  Proof.
    elim: l1 acc => /= [|h1 t1 IH] acc //.
    rewrite !IH //.
    by full_inv_fin.
  Qed.

  Lemma bernoulli_to_geometric_app (l1 l2 : list (fin 2)) :
    bernoulli_to_geometric (l1 ++ [1] ++ l2) 
      = 
    bernoulli_to_geometric (l1 ++ [1]) ++ bernoulli_to_geometric l2.
  Proof.
    apply bernoulli_to_geometric_aux_app.
  Qed.

  Lemma geometric_to_bernoulli_to_geometric (g : list nat) :
    bernoulli_to_geometric (geometric_to_bernoulli g) = g.
  Proof.
    elim: g => /= [|h g IH] //.
    rewrite -app_assoc bernoulli_to_geometric_app IH bernoulli_to_geometric_repeat.
    reflexivity.
  Qed.

  Lemma list_decomposition (l : list (fin 2)) :
    { 
      '(ns, n) 
    | l = (flat_map (fun v => repeat 0 v ++ [1]) ns) ++ repeat 0 n 
    }.
  Proof.
    elim: l => [|h t [[ns n] ->]]; first (by exists ([], 0%nat));
    full_inv_fin; first case ns => [|hns tns];
    by 
      [ exists ([], (S n))
      | exists ((S hns :: tns), n)
      | exists ((0%nat :: ns), n) ].
  Qed.

  Lemma bernoulli_to_geometric_to_bernoulli (b : list (fin 2)) :
    (geometric_to_bernoulli ∘ bernoulli_to_geometric) (b ++ [1])
      = 
    b ++ [1].
  Proof.

    case: (list_decomposition b) => [[ns n] ->].
    elim: ns => [|hns tns IHns] /=; first rewrite bernoulli_to_geometric_repeat //; first rewrite /= app_nil_r //.
    rewrite -!app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat /=.
    simpl in IHns.
    rewrite !app_assoc IHns -!app_assoc //.
  Qed.
  
  Lemma bernoulli_to_geometric_translation
    (v : list (fin 2)) (l : list nat) :
    is_geometric_translation v l 
      ↔ 
    (l = bernoulli_to_geometric v ∧ ∀ l' k, v = l' ++ [k] -> k = 1).
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

  Lemma geometric_to_bernoulli_ends_with_1 (g_tape : list nat) :
    g_tape = [] ∨ ∃ b_tape, b_tape ++ [1%fin] = geometric_to_bernoulli g_tape.
  Proof.
    destruct g_tape as [|g_end g_tape _] using rev_ind; first by left.
    right.
    rewrite /geometric_to_bernoulli flat_map_app /= app_nil_r app_assoc.
    eauto.
  Qed.


End Tape.
#[local] Open Scope R.


Section Geometric.

  Set Default Proof Using "Type*".
  
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli balloc}.

  Definition own_geometric_tape (α : loc) (N M : nat) (t : list nat) : iProp Σ :=
    ∃ l, 
    own_bernoulli_tape α N M l ∗ 
    ⌜is_geometric_translation l t⌝.

  #[local] Ltac done ::= solve[
    lia |
    lra |
    nra |
    tactics.done |
    auto
  ].
  
  Definition geometric_tape : val :=
    rec: "geometric_tape" "α" "N" "M" :=
    if: bernoulli "α" "N" "M" = #1 then #0 else 
    #1 + "geometric_tape" "α" "N" "M"
  .
  Definition geometric : expr := geometric_tape #().

  Lemma geometric_spec 
    (N M k : nat) (Hlt : (N <= M)%nat) (p := N / (S M)) :
  [[{↯ (1 - (((1 - p)^k) * p))%R }]]
    geometric #N #M
  [[{RET #k; True}]].
  Proof.
    assert (0 <= p <= 1)%R as Hp. {
      split; subst p; simpl_expr.
    }
    induction k.
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric /geometric_tape Rmult_1_l.
      wp_pures.
      wp_apply (bernoulli_success_spec_simple with "Herr") as "_".
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric /geometric_tape.
      wp_pures.
      fold geometric_tape geometric.
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

  Lemma twp_presample_geometric
      (e : expr) (α : loc) (N M : nat) (Φ : val → iProp Σ)
      (ns : list nat) :
    to_val e = None → 
    own_geometric_tape α N M ns ∗
    (∀ (i : nat), own_geometric_tape α N M (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (e_not_val) "[
      (%b_tape & Hown_ber & %Hgeo_trans) 
      HΦ
    ]".
    wp_apply (twp_presample_bernoulli e α Φ); first done.
    iFrame.
    iIntros (i) "Hown_ber".
    full_inv_fin; last first.
    - iApply ("HΦ" $! 0%nat).
      iFrame.
      iPureIntro.
      rewrite ->bernoulli_to_geometric_translation in *.
      destruct Hgeo_trans as [-> Hb_end_1].
      destruct b_tape as [| b_end b_tape _] using rev_ind.
      + simpl; split; first done.
        move=> ?? Heq.
        rewrite -(app_nil_l [1%fin]) in Heq.
        by apply list_snoc_singleton_inv in Heq as [_ ->].
      + split; last first. 
        { move=> ?? Heq.
        rewrite -(app_nil_l [1%fin]) in Heq.
        by apply list_snoc_singleton_inv in Heq as [_ ->]. }
        full_inv_fin.
        { move=> Hb_end_1.
          specialize Hb_end_1 with b_tape 0%fin.
          exfalso.
          assert ((0%fin : fin 2) ≠ 1%fin) as contra by by intro.
          by apply contra, Hb_end_1. }
        move=> Hb_end_1.
        rewrite -app_assoc bernoulli_to_geometric_app //.
    - wp_apply twp_presample_bernoulli; first done.
      iFrame.
      iIntros (i) "Hown_ber".
      full_inv_fin; last first.
      + iApply ("HΦ" $! 1%nat).
        iFrame.
        iPureIntro.
        rewrite ->bernoulli_to_geometric_translation in *.
        destruct Hgeo_trans as [-> Hb_end_1].
        destruct b_tape as [| b_end b_tape _] using rev_ind.
        * simpl; split; first done.
          move=> ?? Heq.
          by apply (list_snoc_singleton_inv [0%fin]) in Heq as [_ ->].
        * split; last first. 
          { move=> ?? Heq.
            rewrite -(app_nil_l [1%fin]) in Heq.
            by apply list_snoc_singleton_inv in Heq as [_ ->]. }
          full_inv_fin.
          { move=> Hb_end_1.
            specialize Hb_end_1 with b_tape 0%fin.
            exfalso.
            assert ((0%fin : fin 2) ≠ 1%fin) as contra by by intro.
            by apply contra, Hb_end_1. }
          move=> Hb_end_1.
          rewrite -!app_assoc bernoulli_to_geometric_app //.
      + (* and so on *)
        (* We have to repeat presampling until we have a 1
          Induction with error credit amplification ?
        twp_presample_adv_comp
        *)
  Abort.

  

  Lemma twp_presample_several_geometric
      (e : expr) (α : loc) (N M : nat) (ε : nonnegreal) (Φ : val → iProp Σ)
      (ns : list nat) :
    to_val e = None → 
    (0 < N < S M)%nat →
    0 < ε → 
    ↯ ε ∗
    own_geometric_tape α N M ns ∗
    (∀ (n : nat) (suf : list nat), own_geometric_tape α N M (ns ++ n::suf) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (e_not_val O_lt_N_lt_SM ε_pos) "(
      Herr & 
      (%b_tape & Hown_ber & %Hgeo_trans) &
      HΦ
    )".
    wp_apply (twp_presample_bernoulli_planner N M _ _ 1%nat _ Φ _ (λ _, [1%fin])); [done.. | iFrame].
    iIntros "(%junk & Hown_ber)".
    case: (list_decomposition junk) => [[[|first_junk junk_repeat] junk_zeros] ->] /=.
    - iApply ("HΦ" $! junk_zeros []).
      iFrame.
      iPureIntro.
      apply bernoulli_to_geometric_translation; split; last first.
      { move=>?? Heq.
        rewrite app_assoc in Heq.
        by apply list_snoc_singleton_inv in Heq as [_ ->]. }
      apply 
        bernoulli_to_geometric_translation 
        in Hgeo_trans 
        as [-> btape_ends_1].
      destruct b_tape as [| btape_end b_tape ] using rev_ind.
      { rewrite bernoulli_to_geometric_repeat //. }
      assert (btape_end = 1%fin) as -> by apply (btape_ends_1 b_tape), eq_refl.
      rewrite -!app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat //.
    - rewrite -!app_assoc.
      set tail : list (fin 2) :=  
        (flat_map 
          (λ v : nat, repeat 0%fin v ++ [1%fin]) 
          (junk_repeat))
        ++ 
        repeat 0%fin junk_zeros
        ++ [1%fin]
      .
      iApply ("HΦ" $! first_junk (bernoulli_to_geometric tail)); iFrame.
      iPureIntro.
      apply bernoulli_to_geometric_translation; split; last first.
      { move =>?? Heq.
        unfold tail in *.
        rewrite !app_assoc in Heq.
        by apply list_snoc_singleton_inv in Heq as [_ ->]. }
      apply 
        bernoulli_to_geometric_translation 
        in Hgeo_trans 
        as [-> btape_ends_1].
      destruct b_tape as [| btape_end b_tape ] using rev_ind; first by rewrite bernoulli_to_geometric_app bernoulli_to_geometric_repeat.
      assert (btape_end = 1%fin) as -> by eapply btape_ends_1, eq_refl.
      rewrite 
        -!app_assoc bernoulli_to_geometric_app
        bernoulli_to_geometric_app 
        bernoulli_to_geometric_repeat //.
  Qed.
  Search (?f (_ ++ _) = ?f _ +  ?f _).

  Lemma twp_presample_geometric_planner
    (N M : nat) (e : expr) (ε : nonnegreal)
      (L : nat) (α : loc) (Φ : val → iProp Σ)
      (prefix : list nat) (suffix : list nat → list nat) :
    (0 < N < S M)%nat →
    to_val e = None →
    (∀ junk : list nat,
       (* We have to limit the sum to limit the size of the underlying bernoulli tape *)
       0 < list_sum (suffix (prefix ++ junk)) <= L ∧
       0 < length (suffix (prefix ++ junk)) <= L)%nat → 
    0 < ε →
    ↯ ε ∗ own_geometric_tape α N M prefix ∗
    ( (∃ (junk : list nat), own_geometric_tape α N M (prefix ++ junk ++ suffix (prefix ++ junk))%nat) -∗ WP e [{ Φ }]
    ) ⊢ WP e [{ Φ }].
  Proof.
    iIntros
      (H_0_lt_N_lt_SM He_not_val Hsum_len_suffix ε_pos) 
      "(Herr & (%prefix_ber & Hber_tape & %Hgeo_trans) & HΦ)".
    set suffix2 := fun tape => [1]%fin ++ ((geometric_to_bernoulli ∘ suffix ∘ bernoulli_to_geometric) (tape ++ [1]))%fin.
    wp_apply (
      twp_presample_bernoulli_planner 
        N M e ε (S (L + L)) α Φ prefix_ber suffix2 
        H_0_lt_N_lt_SM He_not_val
    )%nat.
    {
      move=> junk.
      subst suffix2 =>/=.
      rewrite flat_map_length.
      assert ((λ x : nat, length (repeat 0%fin x ++ [1%fin : fin 2])) = S) as ->. {
        apply functional_extensionality => x.
        rewrite app_length repeat_length /length.
        lia.
      }
      rewrite /list_sum /=.
      rewrite foldr_fmap.
      assert ((λ b a, S b + a) = λ b a, 1 + b + a)%nat 
        as ->
        by repeat apply functional_extensionality => b //.
      assert (∀ (l : list nat) (n : nat), foldr (λ b a, n + b + a) 0 l = n * (length l) + foldr Nat.add 0 l)%nat as Hfoldr_add.
      {
        elim => [|h t IH] n //=.
        rewrite IH //.
      }
      rewrite Hfoldr_add /= Nat.add_0_r.
      match goal with 
      | |- ((S (?a + ?b)) ≤ _)%nat=> 
        change (S (a + b)) with (S a + b)%nat
      end.
      change (S (L + L)) with (S L + L)%nat.
      assert (
        (prefix_ber = [] ∧ prefix = []) ∨ 
        ∃ prefix_ber', 
        prefix_ber = prefix_ber' ++ [1%fin] ∧
        prefix = bernoulli_to_geometric (prefix_ber' ++ [1%fin])
      ) as [[-> ->] | (prefix_ber' & -> & ->)]. {
        apply bernoulli_to_geometric_translation in Hgeo_trans as [Heq H_ends_1].
        destruct prefix_ber as [|prefix_ber_end prefix_ber _] using rev_ind; first by subst; left; split.
        assert (prefix_ber_end = 1%fin) as ->.
        { full_inv_fin => _ Hcontra.
          by discriminate (Hcontra prefix_ber 0%fin). }
        eauto.
      }
      all: apply Nat.add_le_mono. 
      all: try apply le_n_S.
      all: try rewrite -!app_assoc (bernoulli_to_geometric_app prefix_ber').
      all: try by destruct (Hsum_len_suffix (bernoulli_to_geometric (junk ++ [1%fin]))) as [[_ Hsum] [_ Hlen]].
    }
    { apply ε_pos. }
    iFrame.
    iIntros "(%junk & Hown)".
    iApply "HΦ".
    subst suffix2. simpl.
    rewrite -{1}(app_nil_l (1::_))%fin app_assoc.
    set junk' := junk ++ [1%fin].
    iExists (bernoulli_to_geometric junk').
    iFrame.
    iPureIntro.
    rewrite bernoulli_to_geometric_translation; split; last first.
    { move=> l' k Heq.
      destruct (geometric_to_bernoulli_ends_with_1 (suffix (bernoulli_to_geometric ((prefix_ber ++ junk) ++ [1%fin])))) 
        as [Heq_nil | (b_tape & Heq_geo)].
      - rewrite Heq_nil /= in Heq.
        apply list_snoc_singleton_inv in Heq.
        by destruct Heq as [_ Heq].
      - rewrite -Heq_geo /= -app_assoc in Heq.
        change (1 :: b_tape ++ [1])%fin with ([1] ++ b_tape ++ [1])%fin in Heq.
        rewrite !app_assoc in Heq.
        apply list_snoc_singleton_inv in Heq.
        by destruct Heq as [_ Heq]. }
    set suf := suffix (bernoulli_to_geometric ((prefix_ber ++ junk))).
    rewrite !app_nil_l bernoulli_to_geometric_app app_assoc !app_nil_r (bernoulli_to_geometric_app (prefix_ber ++ junk)).
    f_equal.
    - apply bernoulli_to_geometric_translation in Hgeo_trans as [Heq H_ends_1].
      destruct prefix_ber as [|prefix_ber_end prefix_ber _] using rev_ind; first by subst.
      assert (prefix_ber_end = 1%fin) as ->.
      { full_inv_fin => _ Hcontra.
        by discriminate (Hcontra prefix_ber 0%fin). }
      rewrite -!app_assoc (bernoulli_to_geometric_app prefix_ber) Heq //.
    - rewrite geometric_to_bernoulli_to_geometric.
      f_equal.
      apply bernoulli_to_geometric_translation in Hgeo_trans as [Heq H_ends_1].
      destruct prefix_ber as [|prefix_ber_end prefix_ber _] using rev_ind; first by subst.
      assert (prefix_ber_end = 1%fin) as ->.
      { full_inv_fin => _ Hcontra.
        by discriminate (Hcontra prefix_ber 0%fin). }
      rewrite -!app_assoc (bernoulli_to_geometric_app prefix_ber) Heq //.
  Qed.
End Geometric.
