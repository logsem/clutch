(** von Neumann Trick *)
From clutch.prelude Require Import tactics.
From clutch.foxtrot Require Import foxtrot lib.conversion lib.min lib.par lib.spawn.

Set Default Proof Using "Type*".

Definition flipL : val := λ: "e", int_to_bool (rand("e") #1%nat).
Definition flip : expr := (flipL #()).

Lemma length_bind {A:Type} (l1 l2: list A): length (l1 ≫= (λ x, (λ y, (x, y)) <$> l2)) = length l1 * length l2.
Proof.
  revert l2.
  induction l1; first done. 
  simpl.
  intros.
  rewrite app_length.
  rewrite fmap_length.
  by f_equal.
Qed. 
  
Section von_neumann.
  Variable (N : nat).
  Variable (ad : val).
  Definition Htyped:= ∅ ⊢ₜ ad : (TRef TNat → TUnit).

  Definition von_neumann_prog: val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "x" := (rand #(S N)) ≤ "bias" in
         let: "y" := (rand #(S N)) ≤ "bias" in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition von_neumann_prog': val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "α" := alloc #(S N)in
         let: "β" := alloc #(S N) in
         let: "x" := (rand("α") #(S N)) ≤ "bias" in
         let: "y" := (rand("β") #(S N)) ≤ "bias" in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition von_neumann_con_prog: val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let, ("x", "y") := (((rand #(S N))≤ "bias") ||| ((rand #(S N))≤ "bias")) in
         if: "x" = "y" then "f" #() else "x"
      ).
  
  Definition von_neumann_con_prog': val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "α" := alloc #(S N)in
         let: "β" := alloc #(S N) in
         let, ("x", "y") := (((rand("α") #(S N))≤ "bias") ||| ((rand("β") #(S N))≤ "bias")) in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition rand_prog: val :=
    λ:"_" "_", flip.
  
  Definition rand_prog': val :=
    λ: "_" "_", let: "x" := alloc #1 in flipL "x" .
  
  Section proof.
    Context `{!foxtrotRGS Σ}.
    
    Lemma wp_von_neumann_prog_von_neumann_prog' K j :
      Htyped->
     j ⤇ fill K (von_neumann_prog' ad) -∗
     WP (von_neumann_prog ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ( () → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_prog'.
      rewrite /von_neumann_prog.
      iPoseProof (binary_fundamental.refines_typed _ [] _ Ht) as "H".
      unfold_rel.
      wp_pures. tp_pures j.
      wp_alloc l as "Hl".
      wp_pures.
      tp_alloc j as l' "Hl'".
      tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'"; first (iFrame; by iExists 0).
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        wp_bind (Val ad).
        tp_bind j' (Val ad).
        iApply (wp_wand with "[Hspec']").
        - by iApply "H".
        - simpl.
          iIntros (?) "(%&Hspec&#Hrel)".
          unfold_rel.
          rewrite -(fill_empty (App _ #l'))%E.
          iApply (wp_wand with "[-]").
          + iApply "Hrel"; last done. iExists _, _. by repeat iSplit.
          +  by iIntros.
      }
      simpl.
      tp_pures j.
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      iLöb as "IH".
      wp_pures.
      tp_pures j.
      wp_bind (! _)%E.
      iInv "Hinv'" as ">(%&%&?&?&[%[-> ->]])" "Hclose".
      tp_load j.
      wp_load.
      iMod ("Hclose" with "[-Hspec]").
      { iFrame. by iExists _. }
      iModIntro.
      wp_apply (wp_min_prog); first done.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      iIntros (? ->).
      simpl.
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      tp_allocnattape j β as "Hβ".
      tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec]"); first naive_solver.
      iIntros (?) "(?&Hspec&%)".
      simpl.
      wp_pures. tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec]"); first naive_solver.
      iIntros (?) "(?&Hspec&%)".
      simpl.
      tp_pures j; first solve_vals_compare_safe.
      wp_pures.
      case_bool_decide.
      - tp_pure j. wp_pure. by iApply "IH".
      - tp_pures j. wp_pure. iFrame.
        by iExists _.
    Qed.
    
    Lemma wp_von_neumann_prog'_rand_prog K j:
      Htyped->
     j ⤇ fill K (Val rand_prog ad) -∗
     WP (Val von_neumann_prog' ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_prog'.
      rewrite /rand_prog.
      wp_pures. tp_pures j.
      wp_alloc l as "Hl".
      wp_pures.
      iMod (inv_alloc _ _ _ with "[Hl]") as "#Hinv"; first shelve.
      wp_apply (wp_fork).
      { iPoseProof (typed_safe _ [] _ Ht) as "H'".
        wp_bind (Val ad).
        iApply (wp_wand); first done.
        simpl.
        iIntros (?) "#H".
        rewrite unary_model.refines_eq.
        rewrite /unary_model.refines_def.
        iApply wp_wand.
        - iApply "H". iExists _; by repeat iSplit.
        - by iIntros. }
      Unshelve.
      2:{ iFrame. by iExists 0. }
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[->->]".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      tp_pures j.
      rewrite /flipL.
      tp_pures j.
      iLöb as "IH".
      wp_pures.
      wp_bind (! _)%E.
      iInv "Hinv" as ">(%&Hl&[% ->])" "Hclose".
      wp_load.
      iMod ("Hclose" with "[$Hl]") as "_"; first by iExists _.
      iModIntro.
      wp_apply wp_min_prog; first done.
      iIntros (?) "->".
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape β as "Hβ".
      wp_pures.
      remember (n`min` N)%Z as x eqn:Heqx.
      assert (0<=x /\ x <= n /\ x <=N)%Z by lia.
      pose (small:= seq 0 (Z.to_nat x+1)%nat).
      pose (large:= seq (Z.to_nat x+1)%nat (S N-Z.to_nat x)).
      pose (l1 := small ≫= (λ x, (λ y, (x, y)) <$> large) ).
      pose (l2 := large ≫= (λ x, (λ y, (x, y)) <$> small) ). 
      tp_bind j (rand _)%E.
      iMod (pupd_couple_von_neumann_1 l1 l2 with "[$Hα][$Hβ][$]") as"H".
      { rewrite /l1. rewrite Forall_forall.
        intros [].
        rewrite elem_of_list_bind.
        rewrite /small/large.
        setoid_rewrite elem_of_list_fmap.
        setoid_rewrite elem_of_seq.
        intros. destruct!/=. lia.
      }
      { rewrite /l2. rewrite Forall_forall.
        intros [].
        rewrite elem_of_list_bind.
        rewrite /small/large.
        setoid_rewrite elem_of_list_fmap.
        setoid_rewrite elem_of_seq.
        intros. destruct!/=. lia.
      }
      { rewrite NoDup_app.
        split!.
        - rewrite /l1.
          rewrite /small/large.
          apply NoDup_bind.
          + setoid_rewrite elem_of_list_fmap.
            setoid_rewrite elem_of_seq.
            intros. destruct!/=. lia.
          + intros.
            apply NoDup_fmap.
            * intros ???. by simplify_eq.
            * apply NoDup_seq.
          + apply NoDup_seq.
        - rewrite /l1 /l2.
          intros [].
          rewrite /small/large.
          rewrite !elem_of_list_bind.
          setoid_rewrite elem_of_list_fmap.
          setoid_rewrite elem_of_seq.
          intros. intros ?. destruct!/=. lia.
        - rewrite /l2.
          rewrite /small/large.
          apply NoDup_bind.
          + setoid_rewrite elem_of_list_fmap.
            setoid_rewrite elem_of_seq.
            intros. destruct!/=. lia.
          + intros.
            apply NoDup_fmap.
            * intros ???. by simplify_eq.
            * apply NoDup_seq.
          + apply NoDup_seq.
      }
      { rewrite /l1/l2.
        rewrite !length_bind. lia. }
      { rewrite !length_bind. rewrite /small/large.
        rewrite !seq_length. destruct!/=.
        apply Nat.mul_pos_pos; lia.
      }
      { rewrite !length_bind/small/large !seq_length. subst.
        assert (∀ x N', x<= N' -> 2* ((x+1) * (S N' - x)) <= (S (S N'))* (S (S N')))%nat as H'.
        - clear.
          intros x N.
          revert x.
          induction N; first lia.
          intros x.
          destruct (decide (x = S n)); first (subst; lia).
          intros. 
          assert (x <=n) as K by lia.
          apply IHn in K. lia.
        - apply H'. lia.
      }
      iDestruct ("H") as "(%&%&%&%&Hα&Hβ&Hspec)".
      simpl.
      case_bool_decide as K1.
      { (* return true *)
        iMod (spec_int_to_bool with "[$]").
        rewrite Z_to_bool_neq_0; last done.
        rewrite /l1 elem_of_list_bind in K1.
        setoid_rewrite elem_of_list_fmap in K1.
        rewrite /large/small in K1.
        setoid_rewrite elem_of_seq in K1.
        destruct!/=.
        wp_randtape.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_randtape.
        wp_pure.
        rewrite bool_decide_eq_false_2; last lia.
        wp_pures.
        iFrame. by iExists _.
      }
      case_bool_decide as K2.
      { (* return false *)
        iMod (spec_int_to_bool with "[$]").
        rewrite Z_to_bool_eq_0. 
        rewrite /l2 elem_of_list_bind in K2.
        setoid_rewrite elem_of_list_fmap in K2.
        rewrite /large/small in K2.
        setoid_rewrite elem_of_seq in K2.
        destruct!/=.
        wp_randtape.
        wp_pures.
        rewrite bool_decide_eq_false_2; last lia.
        wp_randtape.
        wp_pure.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        iFrame. by iExists _.
      }
      rewrite /l1 in K1.
      rewrite /l2 in K2.
      rewrite !elem_of_list_bind/small/large in K1 K2.
      setoid_rewrite elem_of_list_fmap in K1.
      setoid_rewrite elem_of_list_fmap in K2.
      setoid_rewrite elem_of_seq in K1.
      setoid_rewrite elem_of_seq in K2.
      wp_randtape.
      wp_pures.
      wp_randtape.
      case_bool_decide as K3.
      - wp_pure.
        rewrite bool_decide_eq_true_2; last first.
        { apply Znot_gt_le.
          intros ?. apply K1. eexists _.
          split; first eexists _.
          - split; first done. lia.
          - simpl. lia. 
        }
        do 4 wp_pure.
        by iApply "IH".
      - wp_pure.
        rewrite bool_decide_eq_false_2; last first.
        { intros ?. apply K2. eexists _.
          split; first eexists _.
          - split; first done. lia.
          - simpl. lia. 
        }
        do 4 wp_pure.
        by iApply "IH".
    Qed. 
  
  End proof.
  
  
  
  Section proof'.
    Context `{!foxtrotRGS Σ, Hspawn: !spawnG Σ}.

    Lemma wp_rand_prog_rand_prog' K j:
      Htyped->
     j ⤇ fill K (Val rand_prog' ad) -∗
     WP (Val rand_prog ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /rand_prog'.
      rewrite /rand_prog.
      tp_pures j.
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      rewrite /flipL.
      tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_pures.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec]"); first naive_solver.
      iIntros (?) "(?&Hspec&%)".
      simpl.
      iMod (spec_int_to_bool with "[$]").
      wp_apply (wp_int_to_bool); first done.
      iIntros. iFrame.
      by iExists _.
    Qed.
    
    Local Opaque INR.

    
    Lemma wp_rand_prog'_von_neumann_con_prog K j:
      Htyped->
      j ⤇ fill K (Val von_neumann_con_prog ad) -∗
      WP (Val rand_prog' ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /rand_prog'.
      rewrite /von_neumann_con_prog.
      tp_pures j.
      tp_alloc j as l "Hl".
      tp_pures j.
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec _]".
      simpl.
      tp_pures j.
      iMod (inv_alloc nroot _ (l↦ₛ#0)%I with "[$]") as "#Hinv'".
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear K j.
      iIntros (K j) "Hspec".
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      rewrite /flipL.
      wp_pures.
      iMod (pupd_epsilon_err) as "(%&%&Herr)".
      iRevert "Hspec Hα".
      set (k:=(((N+2)* (N+2))%nat / ((N+2)*(N+2) - 2 * (N+1))%nat)%R).
      iApply (ec_ind_simpl _ k with "[][$]"); first done.
      { rewrite /k.
        apply Rcomplements.Rlt_div_r.
        - apply Rlt_gt.
          apply lt_0_INR.
          lia.
        - rewrite Rmult_1_l. apply lt_INR. lia.
      }
      iModIntro.
      iIntros "[Hind Herr] Hspec Hα".
      tp_pures j.
      iApply pupd_wp.
      iInv "Hinv'" as ">?" "Hclose".
      tp_load j.
      iMod ("Hclose" with "[$]") as "_".
      iModIntro.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      simpl.
      rewrite Z.min_l; last lia.
      do 2 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      tp_bind j1 (rand _)%E.
      tp_bind j2 (rand _)%E.
      set (seq 1%nat (S N)) as lis.
      iMod (pupd_couple_von_neumann_2 ((λ x, (0, x)%nat) <$> lis) ((λ x, (x, 0)%nat) <$> lis)with "[$Hspec1][$][$][$]") as "H".
      { rewrite Forall_fmap. rewrite Forall_forall.
        intros ?. rewrite /lis. rewrite elem_of_seq.
        intros. destruct!/=. lia.
      }
      { rewrite Forall_fmap. rewrite Forall_forall.
        intros ?. rewrite /lis. rewrite elem_of_seq.
        intros. destruct!/=. lia.
      }
      { rewrite NoDup_app.
        rewrite /lis.
        repeat split.
        - apply NoDup_fmap.
          + intros ???. by simplify_eq.
          + apply NoDup_seq.
        - intros []. rewrite !elem_of_list_fmap.
          setoid_rewrite elem_of_seq.
          intros. intros ?. destruct!/=. lia.
        - apply NoDup_fmap.
          + intros ???. by simplify_eq.
          + apply NoDup_seq.
      }
      { by rewrite !fmap_length seq_length. }
      { rewrite fmap_length seq_length. lia. }
      { rewrite fmap_length seq_length. lia. }
      { done. }
      rewrite fmap_length seq_length.
      iDestruct "H" as "(%&%&%&%&Hspec1&Hspec2&Hα)".
      case_bool_decide as C1.
      { (* return true *)
        rewrite elem_of_list_fmap/lis in C1.
        setoid_rewrite elem_of_seq in C1.
        destruct!/=.
        tp_pures j1.
        tp_pures j2.
        rewrite bool_decide_eq_false_2; last lia.
        iMod ("Hcont" with "[$]") as "Hspec".
        tp_pures j; first solve_vals_compare_safe.
        wp_randtape.
        wp_apply (wp_int_to_bool); first done.
        iIntros.
        iFrame.
        rewrite Z_to_bool_neq_0; last done.
        by iExists _. }
      case_bool_decide as C2.
      { (* return false *)
        rewrite elem_of_list_fmap/lis in C2.
        setoid_rewrite elem_of_seq in C2.
        destruct!/=.
        tp_pures j1.
        rewrite bool_decide_eq_false_2; last lia.
        tp_pures j2.
        iMod ("Hcont" with "[$]") as "Hspec".
        tp_pures j; first solve_vals_compare_safe.
        wp_randtape.
        wp_apply (wp_int_to_bool); first done.
        iIntros.
        iFrame.
        rewrite Z_to_bool_eq_0.
        by iExists _. }
      simpl.
      tp_pures j1.
      case_bool_decide as C3.
      - tp_pures j2.
        rewrite !elem_of_list_fmap/lis in C1, C2.
        setoid_rewrite elem_of_seq in C1.
        setoid_rewrite elem_of_seq in C2.
        rewrite bool_decide_eq_true_2; last first.
        { apply Z.nlt_ge.
          intros ?. apply C1.
          eexists _; split; first f_equal.
          - simpl in *. lia.
          - lia. }
        iDestruct "Hα" as "[Hα Herr]".
        iMod ("Hcont" with "[$]") as "Hspec".
        do 9 (tp_pure j); first solve_vals_compare_safe.
        tp_pure j.
        iApply ("Hind" with "[Herr][$][$]").
        iApply ec_eq; last done.
        rewrite /k.
        do 3 f_equal; lia.
      - tp_pures j2.
        rewrite !elem_of_list_fmap/lis in C1, C2.
        setoid_rewrite elem_of_seq in C1.
        setoid_rewrite elem_of_seq in C2.
        rewrite bool_decide_eq_false_2; last first.
        { intros ?. apply C2.
          eexists _; split; first (f_equal; lia).
          lia.
        }
        iDestruct "Hα" as "[Hα Herr]".
        iMod ("Hcont" with "[$]") as "Hspec".
        do 9 (tp_pure j); first solve_vals_compare_safe.
        tp_pure j.
        iApply ("Hind" with "[Herr][$][$]").
        iApply ec_eq; last done.
        rewrite /k.
        do 3 f_equal; lia.
    Qed. 
      
    Lemma wp_von_neumann_con_prog_von_neumann_con_prog' K j:
      Htyped ->
      j ⤇ fill K (Val von_neumann_con_prog' ad) -∗
      WP (Val von_neumann_con_prog ad)
        {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_con_prog'.
      rewrite /von_neumann_con_prog.
      iPoseProof (binary_fundamental.refines_typed _ [] _ Ht) as "H".
      unfold_rel.
      wp_pures.
      tp_pures j.
      wp_alloc l as "Hl".
      tp_alloc j as l' "Hl'".
      wp_pures. tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'".
      { iFrame. iNext. iExists 0; iPureIntro; split; f_equal. }
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        wp_bind (Val ad).
        tp_bind j' (Val ad).
        iApply (wp_wand with "[Hspec']").
        - by iApply "H".
        - simpl.
          iIntros (?) "(%&Hspec&#Hrel)".
          unfold_rel.
          rewrite -(fill_empty (App _ #l'))%E.
          iApply (wp_wand with "[-]").
          + iApply "Hrel"; last done. iExists _, _. by repeat iSplit.
          +  by iIntros. 
      }
      simpl.
      tp_pures j.
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear -Hspawn.
      iIntros (K j) "Hspec".
      iLöb as "IH".
      wp_pures.
      tp_pures j.
      wp_bind (! _)%E.
      iInv "Hinv'" as ">(%&%&?&?&[%[-> ->]])" "Hclose".
      tp_load j.
      wp_load.
      iMod ("Hclose" with "[-Hspec]").
      { iFrame. by iExists _. }
      iModIntro.
      wp_apply (wp_min_prog); first done.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      iIntros (? ->).
      simpl.
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      tp_allocnattape j β as "Hβ".
      do 2 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      wp_apply (wp_par (λ v, ∃ (b:bool), ⌜v=#b⌝ ∗ j1 ⤇ fill K1 v)%I (λ v, ∃ (b:bool), ⌜v=#b⌝ ∗ j2 ⤇ fill K2 v)%I with "[Hα Hspec1][Hβ Hspec2]").
      - tp_bind j1 (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec1]"); first naive_solver.
        iIntros (?) "(?&Hspec1&%)".
        simpl.
        tp_pures j1.
        wp_pures.
        iFrame.
        by iExists _.
      - tp_bind j2 (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec2]"); first naive_solver.
        iIntros (?) "(?&Hspec2&%)".
        simpl.
        tp_pures j2.
        wp_pures.
        iFrame.
        by iExists _.
      - iIntros (??) "[(%&->&Hspec1) (%&->&Hspec2)]".
        iNext.
        iMod ("Hcont" with "[$]").
        simpl.
        tp_pures j; first solve_vals_compare_safe.
        wp_pures.
        case_bool_decide.
        + tp_pure j. wp_pure. by iApply "IH".
        + tp_pures j. wp_pure. iFrame.
          by iExists _.
    Qed.
    
    Lemma wp_von_neumann_con_prog'_von_neumann_prog K j:
      Htyped ->
      j ⤇ fill K (Val von_neumann_prog ad) -∗
      WP (Val von_neumann_con_prog' ad)
        {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_con_prog'.
      rewrite /von_neumann_prog.
      iPoseProof (binary_fundamental.refines_typed _ [] _ Ht) as "H".
      unfold_rel.
      wp_pures.
      tp_pures j.
      wp_alloc l as "Hl".
      tp_alloc j as l' "Hl'".
      wp_pures. tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'".
      { iFrame. iNext. iExists 0; iPureIntro; split; f_equal. }
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        wp_bind (Val ad).
        tp_bind j' (Val ad).
        iApply (wp_wand with "[Hspec']").
        - by iApply "H".
        - simpl.
          iIntros (?) "(%&Hspec&#Hrel)".
          unfold_rel.
          rewrite -(fill_empty (App _ #l'))%E.
          iApply (wp_wand with "[-]").
          + iApply "Hrel"; last done. iExists _, _. by repeat iSplit.
          +  by iIntros. 
      }
      
      simpl.
      tp_pures j.
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear -Hspawn.
      iIntros (K j) "Hspec".
      iLöb as "IH".
      wp_pures.
      tp_pures j.
      wp_bind (! _)%E.
      iInv "Hinv'" as ">(%&%&?&?&[%[-> ->]])" "Hclose".
      tp_load j.
      wp_load.
      iMod ("Hclose" with "[-Hspec]").
      { iFrame. by iExists _. }
      iModIntro.
      wp_apply (wp_min_prog); first done.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      iIntros (? ->).
      simpl.
      wp_pures.
      tp_pures j.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape β as "Hβ".
      wp_pures.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hα][$]") as "(%x&Hα&Hspec&%)"; first naive_solver.
      simpl.
      tp_pures j.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hβ][$]") as "(%y&Hβ&Hspec&%)"; first naive_solver.
      simpl.
      tp_pures j; first solve_vals_compare_safe.
      wp_apply (wp_par (λ v, ⌜v=#(bool_decide (x ≤ n `min` N))⌝)%I (λ v, ⌜v=#(bool_decide (y ≤ n `min` N))⌝)%I with "[Hα][Hβ]"); [wp_randtape; by wp_pures..|].
      iIntros (??)"[->->]".
      iNext.
      wp_pures.
      case_bool_decide.
      - tp_pure j. wp_pure. by iApply "IH".
      - tp_pures j. wp_pure. iFrame.
        by iExists _.
    Qed.
    
  End proof'.

  Lemma von_neumann_prog_refines_rand_prog :
    Htyped ->
    ∅ ⊨ von_neumann_prog ad ≤ctx≤ rand_prog ad : (TUnit →TBool).
  Proof.
    intros Ht.
    eapply ctx_refines_transitive with (von_neumann_prog' ad);
    apply (refines_sound (#[foxtrotRΣ])); rewrite /interp/=;
    iIntros; unfold_rel;
      iIntros (K j) "Hspec".
    - by wp_apply (wp_von_neumann_prog_von_neumann_prog' with "[$]").
    - (** this one needs stronger logical relations! *)
      by wp_apply (wp_von_neumann_prog'_rand_prog with "[$]").
  Qed.

  Lemma rand_prog_refines_von_neumann_prog :
    Htyped ->
    ∅ ⊨ rand_prog ad ≤ctx≤ von_neumann_prog ad : (TUnit →TBool).
  Proof.
    intros Ht.
    eapply ctx_refines_transitive with (rand_prog' ad); last eapply ctx_refines_transitive with (von_neumann_con_prog ad); last eapply ctx_refines_transitive with (von_neumann_con_prog' ad);
      apply (refines_sound (#[spawnΣ; foxtrotRΣ])); iIntros; unfold_rel; iIntros (K j) "spec"; simpl.
    - by wp_apply (wp_rand_prog_rand_prog' with "[$]").
    - by wp_apply (wp_rand_prog'_von_neumann_con_prog with "[$]").
    - by wp_apply (wp_von_neumann_con_prog_von_neumann_con_prog' with "[$]").
    - by wp_apply (wp_von_neumann_con_prog'_von_neumann_prog with "[$]").
  Qed.
  
  Lemma von_neumann_prog_eq_rand_prog :
    Htyped ->
    ∅ ⊨ von_neumann_prog ad =ctx= rand_prog ad : (TUnit →TBool).
  Proof.
    intros.
    split; by [apply von_neumann_prog_refines_rand_prog|apply rand_prog_refines_von_neumann_prog].
  Qed.

End von_neumann.


 

