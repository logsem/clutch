From iris.base_logic.lib Require Import token mono_nat.
From Stdlib Require Import ZArith Znumtheory.
From clutch.elton Require Import elton.
From clutch.elton Require Import map.
Set Default Proof Using "Type*".

Open Scope Z_scope.

Section useful_lemmas.
  Lemma INR_div_pos x y: (0<=INR x/INR y)%R.
  Proof.
    destruct y.
    { simpl. rewrite Rdiv_0_r. lra. }
    rewrite Rdiv_def.
    apply Rcomplements.Rle_div_r.
    - apply Rlt_gt.
      apply lt_0_INR; lia.
    - rewrite Rmult_0_l.
      replace 0%R with (INR 0) by done. 
      apply le_INR.
      lia.
  Qed.

  Lemma mod_mult_inverse_unique :
    forall p : Z,
    prime p ->
    forall a b : Z,
    0 < a < p ->
    0 <= b < p ->
    exists! x : Z,
      0 <= x < p /\ (a * x) mod p = b mod p.
  Proof.
    intros p Hprime a b Ha Hb.
    assert (Hp_pos : p > 0) by (destruct Hprime; lia).
    assert (Hp_neq0 : p ≠ 0) by lia.
    assert (Hndiv : ~ (p | a)).
    { intros [k Hk]. destruct Ha as [Ha1 Ha2].
      destruct (Z.eq_dec k 0) as [->|Hk0].
      - lia.
      - assert (Z.abs (p * k) >= p) by (rewrite Z.abs_mul; nia).
        lia. }
    assert (Hrel : rel_prime p a) by (apply prime_rel_prime; auto).
    assert (Hrel' : rel_prime a p) by (apply rel_prime_sym; auto).
    destruct (rel_prime_bezout p a Hrel) as [u v Hbez].
    exists ((v * b) mod p).
    unfold unique. split.
    - split.
      + apply Z_mod_lt. lia.
      + rewrite Zmult_mod.
        rewrite Zmod_mod.
        rewrite <- Zmult_mod.
        replace (a * (v * b)) with ((v * a) * b) by ring.
        assert (Hva : v * a = 1 - u * p) by lia.
        rewrite Hva.
        replace ((1 - u * p) * b) with (b + (- u * b) * p) by ring.
        rewrite Z_mod_plus_full.
        rewrite (Zmod_small b p); lia.
    - intros x' [Hx'_range Hx'_eq].
      assert (Hwit_eq : (a * ((v * b) mod p)) mod p = b mod p).
      { rewrite Zmult_mod. rewrite Zmod_mod. rewrite <- Zmult_mod.
        replace (a * (v * b)) with ((v * a) * b) by ring.
        assert (Hva : v * a = 1 - u * p) by lia.
        rewrite Hva.
        replace ((1 - u * p) * b) with (b + (- u * b) * p) by ring.
        rewrite Z_mod_plus_full.
        rewrite (Zmod_small b p); lia. }
      assert (Hx'_eq' : (a * x') mod p = (a * ((v * b) mod p)) mod p).
      { rewrite Hx'_eq. symmetry. exact Hwit_eq. }
      assert (Hdiff : (a * x' - a * ((v * b) mod p)) mod p = 0).
      { rewrite Zminus_mod.
        rewrite Hx'_eq'.
        rewrite Z.sub_diag.
        reflexivity. }
      assert (Hdiv : (p | a * (x' - (v * b) mod p))).
      { apply Zmod_divides in Hdiff; auto.
        destruct Hdiff as [c Hc].
        exists c.
        replace (a * (x' - (v * b) mod p)) with (a * x' - a * ((v * b) mod p)) by ring.
        lia. }
      assert (Hdiv2 : (p | x' - (v * b) mod p)).
      { apply Gauss with a; auto. }
      destruct Hdiv2 as [k Hk].
      assert (Hx_range : 0 <= (v * b) mod p < p) by (apply Z_mod_lt; lia).
      destruct (Z.eq_dec k 0) as [->|Hk0].
      + lia.
      + exfalso.
        assert (Z.abs (x' - (v * b) mod p) >= p).
        { rewrite Hk. rewrite Z.abs_mul.
          assert (Z.abs p = p) by lia.
          rewrite H. nia. }
        lia.
  Qed.
End useful_lemmas.

Close Scope Z_scope.

Section prog.
  Variable p:nat.
  Variable tries:nat.
  Context (Hprime : prime p).

  Definition zmod : val :=
    λ: "a", "a" `rem` #p.


  (** Note the higher-order reference *)
  Definition arr_new : val :=
    (λ: <>,
       ref (#0, init_map #())).

  Definition arr_push : val :=
    λ: "arr" "v",
      let: "pair" := !"arr" in
      let: "len"  := Fst "pair" in
      let: "m" := Snd "pair" in
      set "m" "len" "v";;
      "arr" <- ("len"+#1, "m");;
      "len".

  Definition arr_get : val :=
    λ: "arr" "i",
      let: "pair" := !"arr" in
      let: "m" := Snd "pair" in
      get "m" "i".

  Definition arr_len : val :=
    λ: "arr",
      let: "pair" := !"arr" in
      Fst ("pair").

  Definition try_spend : val :=
    λ: "budget" <>,
      let: "rem" := !"budget" in
      if: "rem" ≤ #0
      then #false
      else "budget" <- "rem" - #1;; #true.

  Definition try_spend_specialized budget : val :=
    λ: <>,
      let: "rem" := !budget in
      if: "rem" ≤ #0
      then #false
      else budget <- "rem" - #1;; #true.

  (** group operations *)

  (** group_mul st h1 h2 — costs 1 query.
    Returns SOME handle on success, NONEV if budget exhausted
    or either handle is invalid. *)
  Definition group_mul : val :=
    λ: "arr" "f" "h1" "h2",
      if: "f" #() 
      then
        let: "e1" := arr_get "arr" "h1" in
        let: "e2" := arr_get "arr" "h2" in
        match: "e1" with
          NONE => #() #()
        | SOME "a" =>
            match: "e2" with
              NONE => #() #()
            | SOME "b" =>
                SOME (arr_push "arr" (zmod ("a" + "b")))
            end
        end
      else NONEV.
  
  Definition group_mul_specialized arr (f:val): val :=
    λ: "h1" "h2",
      if: f #() 
      then
        let: "e1" := arr_get arr "h1" in
        let: "e2" := arr_get arr "h2" in
        match: "e1" with
          NONE => #() #()
        | SOME "a" =>
            match: "e2" with
              NONE => #() #()
            | SOME "b" =>
                SOME (arr_push arr (zmod ("a" + "b")))
            end
        end
      else NONEV.

  (** group_inv st h — costs 1 query. *)
  Definition group_inv : val :=
    λ: "arr" "f" "h",
      if: "f" #()
      then
        let: "e" := arr_get "arr" "h" in
        match: "e" with
          NONE => #() #()
        | SOME "a" =>
            SOME (arr_push "arr" (zmod (#p-"a")))
        end
      else NONEV.
  
  Definition group_inv_specialized arr (f : val): val :=
    λ: "h",
      if: f #()
      then
        let: "e" := arr_get arr "h" in
        match: "e" with
          NONE => #() #()
        | SOME "a" =>
            SOME (arr_push arr (zmod (#p-"a")))
        end
      else NONEV.

  (** group_eq st h1 h2 — does not cost any query. *)
  Definition group_eq : val :=
    λ: "arr" "h1" "h2",
      let: "e1" := arr_get "arr" "h1" in
      let: "e2" := arr_get "arr" "h2" in
      match: "e1" with
        NONE => #() #()
      | SOME "a" =>
          match: "e2" with
            NONE => #() #()
          | SOME "b" =>
             ("a" = "b")
          end
      end.
  
  Definition group_eq_specialized arr : val :=
    λ: "h1" "h2",
      let: "e1" := arr_get arr "h1" in
      let: "e2" := arr_get arr "h2" in
      match: "e1" with
        NONE => NONEV
      | SOME "a" =>
          match: "e2" with
            NONE => NONEV
          | SOME "b" =>
              ("a" = "b")
          end
      end.

  Definition dlog_game : val :=
    λ: "adv",
      let: "x" := rand (#p - #1) in
      let: "arr" := arr_new #() in

      let: "zero" := arr_push "arr" #1 in
      let: "one" := arr_push "arr" "x" in
      
      let: "budget" := ref #tries in
      let: "f" := try_spend "budget" in
      let: "mul" :=  group_mul "arr" "f" in
      let: "inv" := group_inv "arr" "f" in
      let: "eq"  := group_eq "arr" in

      let: "all" := ("zero", "one", "mul", "inv", "eq") in
      
      (* Adversary receives handles and closures, not arr. *)
      let: "guess" := "adv" "all" in
      "guess" = "x".
  
  Definition dlog_game' : val :=
    λ: "adv",
      let: "x" := drand (#p - #1) in
      let: "arr" := arr_new #() in

      let: "zero" := arr_push "arr" #1 in
      let: "one" := arr_push "arr" "x" in
      
      let: "budget" := ref #tries in
      let: "f" := try_spend "budget" in
      let: "mul" :=  group_mul "arr" "f" in
      let: "inv" := group_inv "arr" "f" in
      let: "eq"  := group_eq "arr" in

      let: "all" := ("zero", "one", "mul", "inv", "eq") in
      
      (* Adversary receives handles and closures, not arr. *)
      let: "guess" := "adv" "all" in
      "guess" = "x".


  (* number of values that are invalid:
     - 1
     - final guess
     - all the collisions
     hence (2+((tries)*(tries+1)/2)%R)
   *)

  Definition adv_type :=((∃: #0 * #0 *
                 (#0 → #0 → (TUnit+#0)) *
                 (#0 → (TUnit+#0)) *
                 (#0 → #0 → TBool)
                         ) → TNat)%ty.

  Section proofs.
    Context `{eltonGS Σ}.
    Context `{tokenG Σ}.
    Context `{mono_natG Σ}.
    (* interp adv_type [] advv *)
    
  End proofs.
  
  Lemma guess_group A:
    ∅ ⊢ₜ A : adv_type ->
             pgl (lim_exec ((dlog_game A), {|heap:=∅; urns:= ∅|})) (λ v, v=#false)
               ((2+((tries)*(tries+3)/2)%R) / p )%R.
  Proof.
    intros Htyped.
    eapply (elton_adequacy_remove_drand (#[eltonΣ; tokenΣ; mono_natΣ]) (dlog_game' A)).
    { simpl. by erewrite typed_remove_drand_expr. }
    { apply Rcomplements.Rdiv_le_0_compat.
      - apply Rplus_le_le_0_compat; first lra.
        apply Rcomplements.Rdiv_le_0_compat; last lra.
        apply Rmult_le_pos; first real_solver.
        apply Rplus_le_le_0_compat; real_solver.
      - apply lt_0_INR. destruct Hprime. lia.
    }
    rewrite /dlog_game'.
    iIntros (? Φ).
    iModIntro. iIntros "Herr HΦ".
    iPoseProof (typed_safe _ [] _ Htyped) as "H".
    wp_bind (A).
    iApply (pgl_wp_wand); first done.
    iIntros (?) "#Hinterp".
    simpl.
    wp_pures.
    wp_apply (wp_drand_thunk _ _ _ _ _ (True)).
    { rewrite rupd_unseal/rupd_def.
      iIntros (?) "$".
      iPureIntro.
      intros.
      simpl.
      eexists _; split; first done.
      f_equal.
      f_equal. 
      instantiate (1:=p-1).
      destruct Hprime. lia. }
    iIntros (l) "[_ Hurn]".
    replace (S _) with p; last first.
    { destruct Hprime. lia. }
    wp_pures.
    rewrite /arr_new.
    wp_pures.
    wp_apply (wp_init_map with "[//]").
    iIntros (lm) "Hm".
    wp_alloc arr as "Harr".
    wp_pures.
    rewrite /arr_push.
    wp_pures. wp_load. wp_pures.
    replace 0%Z with (Z.of_nat 0) by done.
    wp_apply (wp_set with "[$]").
    iIntros "Hm".
    wp_pures.
    wp_pures. wp_store. wp_pures.
    wp_load; wp_pures.
    replace (_+_)%Z with (Z.of_nat 1) by done.
    wp_apply (wp_set with "[$]").
    iIntros "Hm".
    wp_pures.
    replace (_+_)%Z with (Z.of_nat 2); last lia.
    wp_store. wp_pures.
    wp_alloc ltries as "Htries".
    wp_pures.
    rewrite /try_spend.
    wp_pures.
    rewrite -/(try_spend_specialized #ltries).
    rewrite /group_mul. wp_pures.
    rewrite -/(group_mul_specialized #arr (try_spend_specialized _)).
    rewrite /group_inv. wp_pures.
    rewrite -/(group_inv_specialized #arr (try_spend_specialized _)).
    rewrite /group_eq. wp_pures.
    rewrite -/(group_eq_specialized #arr).

    (* ghost resources *)
    iMod (token_alloc) as (γ) "Htoken".
    iMod (mono_nat_own_alloc 1%nat) as "(%γ' & Hauth & #Hfrag)".
    assert (1<p) by (destruct Hprime; lia).

    (* resolve urn to remove 1 *)
    assert (0<=((1 + tries * (tries + 3) / 2) / (p-1)%nat))%R as err_ineq.
    { apply Rcomplements.Rdiv_le_0_compat.
      - apply Rplus_le_le_0_compat; first lra.
        apply Rcomplements.Rdiv_le_0_compat; last lra.
        apply Rmult_le_pos; first real_solver.
        apply Rplus_le_le_0_compat; real_solver.
      - apply lt_0_INR. destruct Hprime. lia. }
    
    iMod (pupd_partial_resolve_urn _ _ (λ x, if bool_decide (x=({[1%Z]} : gset _)) then nnreal_one else mknonnegreal _ err_ineq) _ _ (({[1%Z]} ::( (list_to_set (Z.of_nat <$> seq 0 p))∖{[1%Z]}) ::[]): list (gset _)) with "[$][$]") as "H'".
    { destruct p; last (simpl; set_solver). lia. }
    { simpl. rewrite union_empty_r_L.
      rewrite -union_difference_L; first done.
      set_unfold.
      intros. destruct!/=.
      eexists 1; split; first done.
      rewrite elem_of_seq. lia. }
    { repeat setoid_rewrite NoDup_cons. repeat split; last by apply NoDup_nil.
      - set_unfold. set_solver. 
      - set_solver.
    }
    { set_unfold. intros ?. destruct!/=.
      rename select (∅=_) into Hcontra.
      apply (f_equal size) in Hcontra.
      rewrite size_empty in Hcontra.
      rewrite size_difference in Hcontra.
      - rewrite size_list_to_set in Hcontra.
        + rewrite length_fmap length_seq size_singleton in Hcontra. lia.
        + apply NoDup_fmap; first (intros ???; by simplify_eq).
          apply NoDup_seq.
      - set_unfold.
        intros. destruct!/=.
        exists 1; split; first done.
        rewrite elem_of_seq; lia.
    }
    { intros. set_unfold. destruct!/=; set_solver. }
    { rewrite SeriesC_list; last first.
      - repeat setoid_rewrite NoDup_cons.
        repeat split; last by apply NoDup_nil.
        + set_unfold.
          intros ?. destruct!/=. set_solver.
        + set_solver.
          Local Opaque size. 
      - simpl. rewrite bool_decide_eq_true_2; last done.
        rewrite size_singleton Rmult_1_l.
        rewrite bool_decide_eq_false_2; last (set_unfold; set_solver).
        simpl.
        rewrite size_difference; last first.
        + set_unfold. intros. exists 1. split; first done. rewrite elem_of_seq; lia.
        + rewrite size_list_to_set; last first. 
          * apply NoDup_fmap; first (intros ???; by simplify_eq).
            apply NoDup_seq.
          * rewrite size_singleton.
            rewrite length_fmap length_seq.
            rewrite (Rdiv_def _ (_-_)%nat).
            rewrite Rmult_assoc.
            rewrite (Rmult_comm (/_)%R).
            rewrite Rinv_r; first lra.
            apply not_0_INR; lia.
    }
    { eexists (Rmax _ _).
      intros.
      case_bool_decide.
      - apply Rmax_l.
      - apply Rmax_r. }
    iDestruct "H'" as "(%s'&Herr&Hurn &%)".
    set_unfold. destruct!/=.
    { rewrite bool_decide_eq_true_2; last done.
      by iDestruct (ec_contradict with "[$]") as "[]".
    }
    rewrite bool_decide_eq_false_2; last (set_unfold; set_solver).
    simpl.
  Admitted. 
  
End prog.
