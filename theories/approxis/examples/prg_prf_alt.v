(* (* PRF based on a PRG. *) alternative definitions of intermediary
    steps of the proof, neither allow us to carry out the proof to the end... *)
From clutch.approxis Require Import approxis map prg prf list.
From clutch.approxis.examples Require Import option.
From clutch.approxis Require Export bounded_oracle.
Import prf.bounds_check.

Set Default Proof Using "Type*".

Section defs.

  Context `{PRG}.

  (* to retrieve lemmas, ctrl f this : XCJQSDQSJDKL*)
  (** Parameters of the PRF. *)
  Variable key : nat.
  Variable input : nat.
  Let output : nat := key.

  Let Key : nat := 2^key - 1.
  Let Input : nat := 2^input - 1.
  Let Output : nat := 2^output - 1.

  Local Opaque INR.

  Definition G_lr : val :=
    rec: "f" "v" "x" "i" :=
          if: "i" = #0 then
            "v"
          else if: "x" ≫ ("i"- #1) `rem` #2 = #0 then
            "f" (Fst (prg "v")) "x" ("i" - #1)
          else
            "f" (Snd (prg "v")) "x" ("i" - #1).
  
  (** Generic PRF-based symmetric encryption. *)
  Definition prg_prf : val :=
    λ: "k" "x",
      G_lr "k" "x" #input.

  Definition optionval_to_val (v : val) : val :=
    λ: "x",
      match: "x" with
        | NONE => v
        | SOME "v" => "v"
      end.
  
  (* Hybrid algorithm. *)
  Definition prg_prf_hyb (d : nat) : expr :=
    let: "M" := init_map #() in
    λ: "x",
      let: "p"  := "x" ≫ #(input - d) in (* first d bits of "x" (MSBs) *)
      G_lr
        match: get "M" "p" with
          | NONE   => let: "v" := rand #Key in set "M" "p" "v";; "v"
          | SOME "v" => "v"
        end "x" #(input - d).

  Definition prg_prf_hyb_tape (d : nat) : expr :=
    let: "α" := alloc #Key in
    let: "M" := init_map #() in
    λ: "x",
      let: "p"  := "x" ≫ #(input - d) in (* first d bits of "x" (MSBs) *)
      G_lr
        match: get "M" "p" with
          | NONE   => let: "v" := rand("α") #Key in set "M" "p" "v";; "v"
          | SOME "v" => "v"
        end "x"  #(input - d).

  Definition prg_prf_hyb_and_a_half (d : nat) : expr :=
    let: "M"  := init_map #() in
    λ: "x",
      let: "p'" := "x" ≫ #(input - (S d)) in
      let: "p" := "p'" ≫ #1 in
      G_lr
        (let: "v" := match: get "M" "p" with
          | NONE => let: "v" := rand #Key in
            set "M" "p" "v";; "v"
          | SOME "v" => "v"
        end in
          if: "p'" `rem` #2 = #0 then Fst (prg "v")
          else Snd (prg "v")) "x" #(input - S d).
  
  (** RandML types of the scheme. *)
  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition THybrid := (TInput → TOutput)%ty.
  Definition THybridOpt := (TInput → TOption TOutput)%ty.

  #[local] Instance prg_prf_params : PRF_params := {
      card_key := Key;
      card_input := Input;
      card_output := Output;
    }.

  #[local] Instance prg_prfPRF : PRF :=
    {|
      prf.keygen := (λ: "_", rand #Key)%V;
      prf := prg_prf;
      prf.rand_output := (λ:"_", rand #card_output)%V
    |}.

  Definition PRF_real_rand_aux : val :=
  λ: "adv" "oracle" "PRF_scheme" "Q",
    let: "oracle" := q_calls (get_card_input "PRF_scheme") "Q" "oracle" in
    let: "b'" := "adv" "oracle" in
    "b'".

  Variable adv : val.
  Definition TAdv : type := ((TInput → (TUnit + TOutput)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition q_calls := q_calls #Input.

  Section proofs.
    Context `{!approxisRGS Σ}.

  Lemma refines_fst : ∀ (e e' : expr) τ τ',
    refines top e e' (τ * τ') -∗
    REL Fst e << Fst e' : τ.
  Proof. Admitted.

  Lemma refines_snd : ∀ (e e' : expr) τ τ',
    refines top e e' (τ * τ') -∗
    REL Snd e << Snd e' : τ'.
  Proof. Admitted.

  Section sem_typed.

  Lemma prg_sem_typed : ⊢
    REL prg << prg : lrel_int → lrel_int * lrel_int.
  Proof. Admitted.

  Lemma G_lr_sem_typed : ⊢
    REL G_lr << G_lr : lrel_int → lrel_int → lrel_int → lrel_int.
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /G_lr...
    iLöb as "IH".
    rel_arrow_val; iIntros (v1 v2 [v [eq1 eq2]]); subst.
    rel_arrow_val; iIntros (v1 v2 [x [eq1 eq2]]); subst.
    rel_arrow_val; iIntros (v1 v2 [i [eq1 eq2]]); subst...
    destruct (bool_decide (#i = #0)) eqn:eqi; first (rel_pures_l; rel_pures_r; rel_values)...
    destruct (bool_decide (#((x ≫ (i-1)) `rem` 2) = #0)) eqn:eqx_i...
    - repeat rel_apply (refines_app _ _ _ _ lrel_int);
      first rel_apply "IH"; try rel_values.
      rel_bind_l (prg _). rel_bind_r (prg _).
      rel_apply (refines_bind _ _ _ (lrel_int * lrel_int)); first last.
      { iIntros (v1 v2 G).
        destruct G as [n1 [n2 [n3 [n4 [H1 [H2 [[n [eq1 eq2]] [n' [eq1' eq2']]]]]]]]]; subst...
        rel_values.
      } rel_apply refines_app; first (rel_apply prg_sem_typed).
      rel_values.
    - repeat rel_apply (refines_app _ _ _ _ lrel_int);
      first rel_apply "IH"; try rel_values.
      rel_bind_l (prg _). rel_bind_r (prg _).
      rel_apply (refines_bind _ _ _ (lrel_int * lrel_int)); first last.
      { iIntros (v1 v2 G).
        destruct G as [n1 [n2 [n3 [n4 [H1 [H2 [[n [eq1 eq2]] [n' [eq1' eq2']]]]]]]]]; subst...
        rel_values.
      } rel_apply refines_app; first (rel_apply prg_sem_typed).
      rel_values.
  Qed.


  End sem_typed.
    (** hybrid with parameter = 0 or input *)

    Lemma prf_hyb_0 (Q : nat) : ⊢
      REL PRF_real_rand #true adv prf_scheme #Q
       << PRF_real_rand_aux adv (prg_prf_hyb_tape 0) prf_scheme #Q : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      rewrite /prg_prf_hyb_tape.
      rel_alloctape_r α as "Hα"...
      rel_apply_r refines_init_map_r.
      iIntros (mapref) "Hmap"...
      rewrite /PRF_real_rand; rewrite /PRF_real_rand_aux...
      rewrite /get_keygen...
      rel_apply refines_couple_UT; first done. iFrame.
      iModIntro. iIntros (k Hkbound) "Hα". simpl...
      rewrite /get_prf. rewrite /prf_scheme...
      rewrite /prg_prf...
      rel_bind_l (bounded_oracle.q_calls _ _ _).
      rel_bind_r (bounded_oracle.q_calls _ _ _).
      rel_apply (refines_bind _ _ _ (interp (TInput → (TUnit + TOutput)) [])
        with "[-]").
      2 : {
        iIntros (v v') "H"...
        rel_bind_l (adv _); rel_bind_r (adv _).
        rel_apply (refines_bind with "[H]").
        - rel_apply refines_app; first (rel_apply (refines_typed TAdv); assumption).
          rel_values.
        - iIntros (b b') "H". Unshelve. 2 : { exact nil. } simpl...
          rel_values.
      }
      rewrite /bounded_oracle.q_calls...
      rewrite /get_card_input...
      rel_alloc_l cnt as "Hcnt".
      rel_alloc_r cnt' as "Hcnt'"...
      set (P := (∃ (M : gmap nat val) (q : nat),
            cnt  ↦  #q
          ∗ cnt' ↦ₛ #q
          ∗ map_slist mapref M
          ∗ ((α ↪ₛN (Key;[k]) ∗ ⌜M = ∅⌝) ∨
             (α ↪ₛN (Key;[])  ∗ ⌜M = <[0 := #k]> ∅⌝))
        )%I).
      rel_apply (refines_na_alloc P (nroot.@"prf0")). iSplitL.
      { iExists ∅, 0. iFrame. iLeft. iFrame. iPureIntro; reflexivity. }
      iIntros "#Inv".
      rel_arrow_val.
      iIntros (v1 v2 [x [eq1 eq2]]); subst...
      rel_apply refines_na_inv. iSplitL; first iApply "Inv".
      iIntros "[[%M [%q [Hcnt [Hcnt' [Hmap HαM]]]]] Hclose]".
      rel_load_l; rel_load_r...
      destruct (bool_decide (q < Q)%Z) eqn:HqQ;
      destruct (bool_decide (0 ≤ x)%Z) eqn:Hxpos;
      destruct (bool_decide (x ≤ Input)%Z) eqn:Hxbound;
      try (rel_pures_l; rel_pures_r; rel_apply refines_na_close;
        iFrame; rel_values; iExists #(), #(); iLeft; done)...
      rel_load_l; rel_load_r... rel_store_l; rel_store_r...
      replace ((Z.of_nat input) - 0%nat)%Z with (Z.of_nat input) by lia.
      rel_bind_r (get _ _).

      apply bool_decide_eq_true in HqQ.
      apply bool_decide_eq_true in Hxpos.
      apply bool_decide_eq_true in Hxbound.

      assert (Hxshift : Z.shiftr x input = 0).
      {
        destruct (Z_zerop x) as [eq | eq].
        + rewrite eq. rewrite Z.shiftr_0_l. done.
        + apply Z.shiftr_eq_0; first assumption.
          rewrite (Z.pow_lt_mono_r_iff 2); try lia.
          rewrite /Input in Hxbound.
          pose proof (Z.log2_log2_up_spec x) as G.
          assert (Hlogx : (0 < x)%Z).
          {
            apply Zle_lt_or_eq in Hxpos.
            destruct Hxpos as [H1 | H2]; first assumption.
            exfalso. apply eq. symmetry; apply H2. 
          }
          apply G in Hlogx. destruct Hlogx as [Hlogx _].
          apply (Z.le_lt_trans _ x).
          * apply Hlogx.
          * clear -Hxbound.
            replace (Z.of_nat (2 ^ input - 1)%nat) with (2 ^ input - 1)%Z
            in Hxbound; first lia.
            rewrite Nat2Z.inj_sub; first
            (rewrite Nat2Z.inj_pow; lia).
            apply fin.pow_ge_1. lia.
      }
      rewrite Hxshift.
      rel_apply (refines_get_r with "[-Hmap]"); last by iAssumption.
      iIntros (res) "Hmap %Hres".
      iDestruct "HαM" as "[[Hα %HM] | [Hα %HM]]"; subst.
      - rewrite lookup_empty. simpl...
        rel_apply (refines_rand_r with "[Hα]"); first by iAssumption.
        iIntros "Hα _"...
        rel_apply (refines_set_r with "[-Hmap]"); last by iAssumption.
        iIntros "Hmap"... rel_apply refines_na_close; iFrame.
        iSplitL.
        { iExists (<[0:=#k]> ∅), (q + 1).
          replace (Z.of_nat (q+1)%nat) with (q+1)%Z by lia.
          iFrame. iRight. iFrame. iPureIntro. reflexivity. 
        }
        rel_apply refines_injr.
        repeat rel_apply (refines_app _ _ _ _ lrel_int);
        try (iPoseProof G_lr_sem_typed as "H"; iApply "H");
        try rel_values.
      - rewrite lookup_insert... rel_apply refines_na_close; iFrame.
        iSplitL.
        { iExists (<[0:=#k]> ∅), (q + 1).
          replace (Z.of_nat (q+1)%nat) with (q+1)%Z by lia.
          iFrame. iRight. iFrame. iPureIntro. reflexivity. 
        }
        rel_apply refines_injr.
        repeat rel_apply (refines_app _ _ _ _ lrel_int);
        try (iPoseProof G_lr_sem_typed as "H"; iApply "H");
        try rel_values.
  Qed.

    Lemma prf_hyb_input (Q : nat) : ⊢
      REL PRF_real_rand_aux adv (prg_prf_hyb input) prf_scheme #Q
       << PRF_real_rand #false adv prf_scheme #Q : lrel_bool.
    Proof with (rel_pures_l; rel_pures_r).
      rewrite /PRF_real_rand_aux; rewrite /PRF_real_rand...
      rewrite /prg_prf_hyb...
      rel_apply refines_init_map_l.
      iIntros (mapref) "Hmap"...
      rewrite /get_keygen...
      rel_apply refines_randU_r.
      iIntros (k) "%Hkbound". simpl.
      rewrite /get_card_output... rewrite /random_function...
      rel_apply refines_init_map_r.
      iIntros (mapref') "Hmap'"...
      rel_bind_l (bounded_oracle.q_calls _ _ _);
      rel_bind_r (bounded_oracle.q_calls _ _ _).
      rel_apply (refines_bind _ _ _ (interp (TInput → (TUnit + TOutput)) []) with "[-]").
      2 : {
        iIntros (v v') "H"...
        rel_bind_l (adv _); rel_bind_r (adv _).
        rel_apply (refines_bind with "[H]").
        - rel_apply refines_app; first (rel_apply (refines_typed TAdv); assumption).
          rel_values.
        - iIntros (b b') "H". Unshelve. 2 : { exact nil. } simpl...
          rel_values.
      }
      rewrite /bounded_oracle.q_calls.
      rewrite /get_card_input...
      rel_alloc_l cnt as "Hcnt".
      rel_alloc_r cnt' as "Hcnt'"...
      set (P := (∃ (M : gmap nat val) (q : nat),
            cnt ↦ #q
          ∗ cnt' ↦ₛ #q
          ∗ map_list mapref M
          ∗ map_slist mapref' M
          ∗ ⌜ (size (M) <= q)%nat ⌝
          ∗ ⌜ ∀ x, x ∈ (dom M) -> (x < S Input)%nat ∧
                                  (∃ (n : nat), M !! x = Some #n ∧ n < S Key)⌝
        )%I).
        rel_apply (refines_na_alloc P (nroot.@"prfinput")). iSplitL.
        {
          iExists ∅, 0. replace (Z.of_nat 0%nat) with 0%Z by lia. iFrame.
          iPureIntro. split; done.
        }
        iIntros "#Inv".
        rel_arrow_val.
        iIntros (v1 v2 [x [eq1 eq2]]); subst...
        rel_apply refines_na_inv; iSplit; first iApply "Inv".
        iIntros "[[%M [%q [Hcnt [Hcnt' [Hmap [Hmap' >[%HsizeM %Hdom]]]]]]] Hclose]".
        rel_load_l; rel_load_r...
        destruct (bool_decide (q < Q)%Z) eqn:HqQ;
        destruct (bool_decide (0 ≤ x)%Z) eqn:Hxpos;
        destruct (bool_decide (x ≤ Input)%Z) eqn:Hxbound;
          try (rel_pures_l; rel_pures_r; rel_apply refines_na_close; iFrame;
            iSplit; last (rel_values; iExists #(), #(); iLeft; done);
            iPureIntro; split; assumption)...
        rel_load_l; rel_load_r...
        rel_store_l; rel_store_r...
        replace (input - input)%Z with 0%Z by lia.
        rewrite Z.shiftr_0_r.
        apply bool_decide_eq_true in HqQ.
        apply bool_decide_eq_true in Hxpos.
        apply bool_decide_eq_true in Hxbound.
        replace x with (Z.of_nat (Z.to_nat x)) by lia.
        rel_apply (refines_get_l with "[-Hmap]"); last by iAssumption.
        iIntros (res) "Hmap %Hres"; subst.
        rel_apply (refines_get_r with "[-Hmap']"); last by iAssumption.
        iIntros (res) "Hmap' %Hres"; subst.
        destruct (M !! Z.to_nat x) as [v|] eqn:eq; simpl...
        - rewrite /G_lr... rel_apply refines_na_close; iFrame. iSplitL.
          2 : { rel_values. iExists v, v. iModIntro. iRight. repeat iSplit; try done.
            apply elem_of_dom_2 in eq as Hindom. apply Hdom in Hindom.
            destruct Hindom as [_ [n [eq' _]]].
            rewrite eq' in eq. injection eq. clear eq' eq. intro eq.
            rewrite -eq. iExists n. done. }
          iExists M, (q+1). replace (Z.of_nat (q+1)%nat) with (q+1)%Z by lia. iFrame.
          iSplit; iPureIntro; first lia.
          apply Hdom.
        - rewrite /Output. rewrite /output. fold Key.
          rel_apply refines_couple_UU; first done.
          iIntros (n Hnbound). iModIntro...
          rel_apply (refines_set_l with "[-Hmap]"); last iAssumption.
          iIntros "Hmap".
          rel_apply (refines_set_r with "[-Hmap']"); last iAssumption.
          iIntros "Hmap'"...
          rewrite /G_lr...
          rel_apply refines_na_close. iFrame. iSplitL;
          last (rel_values; rewrite /lrel_car; simpl; iExists #n, #n; iRight;
            iModIntro; repeat iSplit; try done; iExists n; done).
          iExists (<[Z.to_nat x:=#n]> M), (q+1).
          replace (Z.of_nat (q+1)%nat) with (q+1)%Z by lia; iFrame.
          iSplit; iPureIntro.
          + rewrite map_size_insert.
            destruct (M !! Z.to_nat x); simpl.
            * eapply Nat.le_trans; first apply HsizeM. done.
            * replace (q+1) with (S q) by lia. apply le_n_S. apply HsizeM.
          + iIntros (elem Hindom).
            rewrite dom_insert in Hindom.
            rewrite elem_of_union in Hindom.
            destruct Hindom as [Heq | Hindom].
            * apply elem_of_singleton in Heq; subst.
              split; first lia.
              exists n. split; first apply lookup_insert.
              lia.
            * apply Hdom in Hindom. destruct Hindom as [Hineqelem [m [Hlookupelem Hboundelem]]].
              split; first assumption.
              destruct (PeanoNat.Nat.eq_dec (Z.to_nat x) elem) as [e|e].
              { exists n. split; last lia. rewrite e. apply lookup_insert. }
              { exists m. split; last assumption.
                rewrite lookup_insert_ne; assumption. }
    Qed.

    (** small step hybrid *)

    Lemma prf_hyb_d_halfd (Q : nat) (l : nat) (Hlbound : l < input) : ⊢
      REL PRF_real_rand_aux adv (prg_prf_hyb l) prf_scheme #Q
       << PRF_real_rand_aux adv (prg_prf_hyb_and_a_half l) prf_scheme #Q : lrel_bool.
    Proof with (rel_pures_l; rel_pures_r).
      rewrite /PRF_real_rand_aux.
      rewrite /prg_prf_hyb. rewrite /prg_prf_hyb_and_a_half...
      rel_apply refines_init_map_l.
      iIntros (mapref) "Hmap".
      rel_apply refines_init_map_r.
      iIntros (mapref_inf) "Hmapinf"...
      rel_bind_l (bounded_oracle.q_calls _ _ _);
      rel_bind_r (bounded_oracle.q_calls _ _ _).
      rel_apply (refines_bind _ _ _ (interp (TInput → (TUnit + TOutput)) [])
        with "[-]").
      2 : {
        iIntros (v v') "H"...
        rel_bind_l (adv _); rel_bind_r (adv _).
        rel_apply (refines_bind with "[H]").
        - rel_apply refines_app; first (rel_apply (refines_typed TAdv); assumption).
          rel_values.
        - iIntros (b b') "H". Unshelve. 2 : { exact nil. } simpl...
          rel_values.
      }
      rewrite /bounded_oracle.q_calls.
      rewrite /get_card_input...
      rel_alloc_l cnt as "Hcnt".
      rel_alloc_r cnt' as "Hcnt'"...
      set (P := (∃ (M : gmap nat val) (q : nat),
          cnt  ↦  #q
        ∗ cnt' ↦ₛ #q
        ∗ map_list  mapref     M
        ∗ map_slist mapref_inf M
      )%I).
      rel_apply (refines_na_alloc P (nroot.@"prf_half_inf")). iSplitL.
      {
        iExists ∅, 0; iFrame.
      }
      iIntros "#Inv".
      rel_arrow_val.
      iIntros (v1 v2 [x [eq1 eq2]]); subst...
      rel_apply refines_na_inv; iSplitL; first iApply "Inv".
      iIntros "[[%M [%q [Hcnt [Hcnt' [Hmap Hmapinf]]]]] Hclose]".
      rel_load_l; rel_load_r...
      destruct (bool_decide (q < Q)%Z) eqn:HqQ;
      destruct (bool_decide (0 ≤ x)%Z) eqn:Hxpos;
      destruct (bool_decide (x ≤ Input)%Z) eqn:Hxbound;
      try (rel_pures_l; rel_pures_r; rel_apply refines_na_close; iFrame;
        rel_values; iExists #(), #(); iLeft; done)...
      apply bool_decide_eq_true in HqQ.
      apply bool_decide_eq_true in Hxpos.
      apply bool_decide_eq_true in Hxbound.
      rel_load_l; rel_load_r...
      rel_store_l; rel_store_r...
      rewrite Z.shiftr_shiftr; last done.
      replace (input - (S l) + 1)%Z with (input - l)%Z by lia.
      pose proof (Z.shiftr_nonneg x (input - l)) as Hxshiftpos'.
      apply Hxshiftpos' in Hxpos as Hxshiftpos. clear Hxshiftpos'.
      pose proof (Z.shiftr_nonneg x (input - S l)) as Hxshiftpos'.
      apply Hxshiftpos' in Hxpos as Hxshiftpos_S. clear Hxshiftpos'.
      replace (Z.shiftr x (input - l))%Z
        with (Z.of_nat (Z.to_nat (Z.shiftr x (input - l))%Z)) by lia.
      rel_apply (refines_get_l with "[-Hmap]"); last iAssumption.
      iIntros (res) "Hmap %Hres"; subst.
      rel_apply (refines_get_r with "[-Hmapinf]"); last iAssumption.
      iIntros (res) "Hmapinf %Hres"; subst.
      destruct (M !! Z.to_nat (x ≫ (input - l))) as [v|] eqn:eqlookupp; simpl...
      - replace (Z.shiftr x (input - S l))%Z
          with (Z.of_nat (Z.to_nat (Z.shiftr x (input - S l))%Z)) by lia.
        pose proof (Nat.div_mod_eq (Z.to_nat (x ≫ (input - S l))) 2) as Hxbase2.
        assert (eqshiftdiv : Z.to_nat (x ≫ (input - S l)) `div` 2
          = Z.to_nat (x ≫ (input - l))).
        {
          replace 2 with (Z.to_nat (2^1)) by lia.
          rewrite -Z2Nat.inj_div; try assumption; try lia.
          rewrite -Z.shiftr_div_pow2; last lia.
          rewrite Z.shiftr_shiftr; last lia.
          replace (input - S l + 1)%Z with (input - l)%Z;
          first reflexivity.
          replace (Z.of_nat (S l))%Z with (l + 1)%Z by lia.
          rewrite Z.sub_add_distr.
          rewrite Z.sub_add. reflexivity.
        }
        rewrite eqshiftdiv in Hxbase2.
        pose proof (Nat.mod_upper_bound (Z.to_nat (Z.shiftr x (input - S l))) 2)
          as Hxshiftbound'.
        assert (Hxshiftbound : 2 ≠ 0) by lia.
        apply Hxshiftbound' in Hxshiftbound. clear Hxshiftbound'.
        destruct (Z.to_nat (x ≫ (input - S l)) `mod` 2) as [|n'] eqn:eqxshift1;
        last destruct n' as [|n''] eqn:eqxshift2; last
          (inversion Hxshiftbound as [H1 | H1 H2 H3];
          inversion H2 as [H1' | H4 H5 H6]; inversion H5); clear Hxshiftbound.
        + rewrite /G_lr. rel_pures_l.
          assert (eqinputl : bool_decide (#(input - l) = #0) = false).
          {
            clear -Hlbound. apply lt_minus_O_lt in Hlbound.
            apply Nat.lt_neq in Hlbound.
            apply bool_decide_eq_false. intro contra.
            injection contra. clear contra. intro contra. lia.
          }
          rewrite eqinputl; clear eqinputl. rel_pures_l.
          replace (Z.of_nat input - Z.of_nat l - 1)%Z
            with (Z.of_nat input - Z.of_nat (S l))%Z by lia.
          replace ((Z.shiftr x (Z.of_nat input - Z.of_nat (S l))))
            with (Z.of_nat (Z.to_nat (Z.shiftr x (Z.of_nat input - Z.of_nat (S l)))))
              by lia.
          rewrite Hxbase2. rewrite Nat.add_0_r.
          rewrite Z2Nat.id; last apply Nat2Z.is_nonneg.
          rel_pures_l.
          assert (eqlastbit :
            (Z.rem
              (Z.of_nat (2 * Z.to_nat (x ≫ (Z.of_nat input - Z.of_nat l)))) 2) = 0).
          {
            rewrite Nat2Z.inj_mul.
            replace (Z.of_nat 2) with 2%Z by lia.
            apply Z.mul_rem. lia.
          }
          rewrite eqlastbit; clear eqlastbit.
          replace (Z.of_nat 0%nat) with 0%Z by lia. rel_pures_l.
          rewrite -/G_lr.
          replace (Z.of_nat input - Z.of_nat l - 1)%Z with
            (Z.of_nat input - Z.of_nat (S l))%Z by lia...
          rel_apply refines_na_close; iFrame.
          iSplitL.
          {
            iExists M, (q+1). replace (Z.of_nat (q+1)) with (q+1)%Z by lia.
            iFrame.
          }
          rel_apply refines_injr.
          repeat (rel_apply (refines_app _ _ _ _ lrel_int));
            try rel_apply G_lr_sem_typed;  
            try rel_values.
          rel_apply refines_fst.
          rel_apply refines_app; first rel_apply prg_sem_typed.
          rel_values. admit.
        + rewrite /G_lr. rel_pures_l.
          assert (eqinputl : bool_decide (#(input - l) = #0) = false).
          {
            clear -Hlbound. apply lt_minus_O_lt in Hlbound.
            apply Nat.lt_neq in Hlbound.
            apply bool_decide_eq_false. intro contra.
            injection contra. clear contra. intro contra. lia.
          }
          rewrite eqinputl; clear eqinputl. rel_pures_l.
          replace (Z.of_nat input - Z.of_nat l - 1)%Z
            with (Z.of_nat input - Z.of_nat (S l))%Z by lia.
          replace ((Z.shiftr x (Z.of_nat input - Z.of_nat (S l))))
            with (Z.of_nat (Z.to_nat (Z.shiftr x (Z.of_nat input - Z.of_nat (S l)))))
              by lia.
          rewrite Hxbase2.
          rewrite Z2Nat.id; last apply Nat2Z.is_nonneg.
          rel_pures_l.
          assert (eqlastbit :
            (Z.rem
              (Z.of_nat (2 * Z.to_nat (x ≫ (Z.of_nat input - Z.of_nat l)) + 1)) 2) = 1).
          {
            rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_mul.
            replace (Z.of_nat 2) with 2%Z by lia.
            replace (Z.of_nat 1) with 1%Z by lia.
            rewrite Z.add_comm.
            rewrite Z.mul_comm.
            apply Z.rem_add; lia.
          }
          rewrite eqlastbit; clear eqlastbit.
          replace (Z.of_nat 1%nat) with 1%Z by lia. rel_pures_l.
          rewrite -/G_lr.
          replace (Z.of_nat input - Z.of_nat l - 1)%Z with
            (Z.of_nat input - Z.of_nat (S l))%Z by lia...
          rel_apply refines_na_close; iFrame.
          iSplitL.
          {
            iExists M, (q+1). replace (Z.of_nat (q+1)) with (q+1)%Z by lia.
            iFrame.
          }
          rel_apply refines_injr.
          repeat (rel_apply (refines_app _ _ _ _ lrel_int));
            try rel_apply G_lr_sem_typed;  
            try rel_values.
          rel_apply refines_snd.
          rel_apply refines_app; first rel_apply prg_sem_typed.
          admit.
      - rel_apply refines_couple_UU; first done.
        iIntros (n Hnbound). iModIntro...
        rel_apply (refines_set_l with "[-Hmap]"); last iAssumption.
        iIntros "Hmap".
        rel_apply (refines_set_r with "[-Hmapinf]"); last iAssumption.
        iIntros "Hmapinf"...
        rewrite /G_lr. rel_pures_l.
        assert (eqinputl : bool_decide (#(input - l) = #0) = false).
        {
          clear -Hlbound. apply lt_minus_O_lt in Hlbound.
          apply Nat.lt_neq in Hlbound.
          apply bool_decide_eq_false. intro contra.
          injection contra. clear contra. intro contra. lia.
        }
        rewrite eqinputl; clear eqinputl. rel_pures_l.
        replace (Z.of_nat input - Z.of_nat l - 1)%Z
          with (Z.of_nat input - Z.of_nat (S l))%Z by lia.
        replace ((Z.shiftr x (Z.of_nat input - Z.of_nat (S l))))
          with (Z.of_nat (Z.to_nat (Z.shiftr x (Z.of_nat input - Z.of_nat (S l)))))
            by lia.
        destruct (bool_decide (#(Z.to_nat (x ≫ (input - S l)) `rem` 2) = #0));
        rewrite -/G_lr; rel_pures_l; rel_pures_r;
         replace (Z.of_nat input - Z.of_nat l - 1)%Z
          with (Z.of_nat input - Z.of_nat (S l))%Z by lia;
          rel_apply refines_na_close; iFrame;
          iSplitL; try (iExists (<[Z.to_nat (x ≫ (input - l)):=#n]> M), (q+1);
            replace (Z.of_nat (q+1)%nat) with (q+1)%Z by lia; iFrame
          );
          try (rel_apply refines_injr;
          repeat (rel_apply (refines_app _ _ _ _ lrel_int));
            try rel_apply G_lr_sem_typed;  
            try rel_values);
          first rel_apply refines_fst; last rel_apply refines_snd;
          rel_apply refines_app; try rel_apply prg_sem_typed; rel_values.
  Admitted.

  Lemma prf_hyb_halfd_Sd (Q : nat) (l : nat) (Hlbound : l < input) : ⊢
    REL PRF_real_rand_aux adv (prg_prf_hyb_and_a_half l) prf_scheme #Q
      << PRF_real_rand_aux adv (prg_prf_hyb (S l)) prf_scheme #Q : lrel_bool.
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /PRF_real_rand_aux.
    rewrite /prg_prf_hyb_and_a_half; rewrite /prg_prf_hyb...
    rel_apply refines_init_map_l.
    iIntros (mapref) "Hmapref".
    rel_apply refines_init_map_r.
    iIntros (mapref') "Hmapref'"...
    rel_bind_l (bounded_oracle.q_calls _ _ _).
    rel_bind_r (bounded_oracle.q_calls _ _ _).
    rel_apply (refines_bind _ _ _ (interp (TInput → (TUnit + TOutput)) []) with "[-]").
    2 : {
      iIntros (v v') "H"...
      rel_bind_l (adv _); rel_bind_r (adv _).
      rel_apply (refines_bind with "[H]").
      - rel_apply refines_app; first (rel_apply (refines_typed TAdv); assumption).
        rel_values.
      - iIntros (b b') "H". Unshelve. 2 : { exact nil. } simpl...
        rel_values.
    }
    rewrite /bounded_oracle.q_calls.
    rewrite /get_card_input...
    rel_alloc_l cnt as "Hcnt".
    rel_alloc_r cnt' as "Hcnt'"...
    set (P := (∃ (M : gmap nat val) (q : nat),
        cnt  ↦  #q
      ∗ cnt' ↦ₛ #q
      ∗ map_list  mapref  M
      ∗ map_slist mapref' M
      ∗ ⌜∀ (x : nat) (v : val), M !! x = Some v -> (∃ n, v = #n)⌝
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"prfhybd_Sd")).
    iSplitL.
    {
      iExists ∅, 0. iFrame.
      iPureIntro. intros * contra. inversion contra.
    }
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (v1 v2 [x [eq1 eq2]]); subst...
    rel_apply refines_na_inv; iSplitL; first iApply "Inv".
    iIntros "[[%M [%q [Hcnt [Hcnt' [Hmap [Hmap' >%HimgM]]]]]] Hclose]".
    rel_load_l; rel_load_r...
    destruct (bool_decide (q < Q)%Z) eqn:Hqbound;
    destruct (bool_decide (0 ≤ x)%Z) eqn:Hxpos;
    destruct (bool_decide (x ≤ Input)%Z) eqn:Hxbound;
    try (rel_pures_l; rel_pures_r; rel_apply refines_na_close;
      iFrame; iSplit; first (iPureIntro; apply HimgM);
      rel_values; iModIntro; rewrite /lrel_car; simpl;
      iExists #(), #(); iLeft; done)...
    rel_load_l; rel_load_r... rel_store_l; rel_store_r...
    replace (Z.shiftr (Z.shiftr x (input - S l)) 1) with
      (Z.of_nat (Z.to_nat (Z.shiftr (Z.shiftr x (input - S l)) 1)));
    replace (Z.shiftr x (input - S l)) with
      (Z.of_nat (Z.to_nat (Z.shiftr x (input - S l)))).
    - rel_apply (refines_get_l with "[-Hmap]"); last iAssumption.
      iIntros (res) "Hmap %Heq"; subst. 
Admitted.
(* here, wr can prove d-1 <~> d,5 but not d,5 <~> d *)




 
  End proofs.


End defs.

(* XCJQSDQSJDKL
  Lemma seq_S_len : forall (start len : nat),
    seq start (S len) = seq start len ++ [start + len].
  Proof. intros start len; generalize dependent start; induction len as [|len' IHlen];
    intro start.
    - simpl. rewrite Nat.add_0_r. reflexivity.
    - simpl. simpl in IHlen. rewrite IHlen.
      simpl. replace (start + S len') with (S (start + len')) by lia.
      reflexivity.
  Qed.

  Lemma fold_left_last : forall (last init : nat) (l : list nat),
    fold_left Nat.add (l ++ [last]) init = fold_left Nat.add l init + last.
  Proof. intros last init l. generalize dependent last.
    generalize dependent init. induction l as [|h t IHt]; intros init last.
    - simpl. reflexivity.
    - simpl. rewrite IHt. reflexivity.
  Qed. 

  Lemma lt_numR : forall (p1 p2 q : R),
    (0 < q)%R -> (p1 <= p2)%R -> (p1 / q <= p2 / q)%R.
  Proof. intros * H1 H2. apply Rcomplements.Rle_div_l; first apply H1.
    rewrite -Rmult_div_swap. rewrite -Rmult_div_assoc.
    rewrite Rdiv_diag.
    - rewrite Rmult_1_r. apply H2.
    - symmetry. apply Rlt_not_eq. apply H1.
  Qed.

  Lemma sum_seq_0_q : forall (n : nat),
    INR (fold_left Nat.add (seq 0 n) 0) = ((INR ((n - 1) * n)) / 2)%R.
  Proof. intros *. induction n as [|n' IHn].
    - simpl. real_solver.
    - rewrite seq_S_len. rewrite fold_left_last.
      rewrite plus_INR. rewrite IHn. simpl.
      replace (n' - 0) with n' by lia.
      replace (INR n') with ((2 * INR n')/2)%R by real_solver.
      rewrite -Rdiv_plus_distr.
      apply Rdiv_eq_compat_r. Set Printing Coercions.
      replace (2%R) with (INR 2) by real_solver.
      rewrite -mult_INR. rewrite -plus_INR.
      assert ((n' - 1) * n' + 2 * n' = n' * S n').
      { rewrite Nat.mul_sub_distr_r.
        rewrite Nat.mul_succ_r.
        replace (1 * n') with n' by lia.
        rewrite -Nat.add_sub_swap; last (induction n'; lia).
        rewrite -Nat.add_sub_assoc; last (induction n'; lia).
        simpl. replace (n' + 0) with n' by lia.
        rewrite -Nat.add_sub_assoc; last (induction n'; lia).
        replace (n' - n') with 0 by lia.
        replace (n' + 0) with n' by lia. reflexivity. }
      rewrite H; reflexivity.
  Qed.
*)