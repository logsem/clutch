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
        NONE =>#() #()
      | SOME "a" =>
          match: "e2" with
            NONE => #()#()
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

    Definition map_match (m:gmap nat base_lit) (m': gmap nat (nat * nat)) l:=
      ∀ k bl (a b:nat),  m!!k=Some bl -> m'!!k= Some (a,b) ->
                     ∀ f x, (0<=x<p)%Z ->
                     f!!l=Some x ->
                     urn_subst f bl = Some (LitInt ( (a*x+b) mod p)%Z).

    Definition no_coll (a b a' b': nat) (s:gset Z) :=
                    ∀ x, (a≠a'\/b≠b') ->
                        x∈s ->
                        ((a*x+b) mod p)%Z ≠ ((a'*x+b') mod p)%Z .

    Lemma no_coll_swap a b a' b' s:
      no_coll a b a' b' s -> no_coll a' b' a b s.
    Proof.
      rewrite /no_coll. intros.
      naive_solver.
    Qed. 

    Definition map_no_coll (m':gmap nat (nat*nat)) s:=
      ∀ k k' (a b a' b':nat), m'!!k=Some (a,b) ->
                              m'!!k'=Some (a',b') ->
                              no_coll a b a' b' s.

    
    Lemma pupd_reduce_urn_list (m':gmap nat (nat*nat)) (a b:nat) (t:nat) (r:R) E (s:gset Z) l:
      size m' = t ->
      (t< size s)%nat ->
      (0<=r) %R ->
      0<=a<p -> 0<=b<p ->
      map_Forall (λ _ x, 0<=x.1<p /\ 0<=x.2<p) m' ->
      set_Forall (λ x : Z, (0 ≤ x < p)%Z) s ->
      ↯((r + t)/ size s) -∗
      l ↪ urn_unif s -∗
      pupd E E (∃ (s':gset Z),
            ⌜s'⊆s⌝ ∗
            ⌜size s - t <=size s' ⌝ ∗
            ⌜(∀ k a' b', m'!!k=Some (a', b') -> no_coll a b a' b' s')⌝ ∗
            l↪ urn_unif s' ∗
            ↯ (r/size s')
        ).
    Proof.
    Admitted. 
      
    
    Definition dlog_inv (lm:loc) arr ltries l γ1 γ2 :=
      ( ∃ (m:gmap nat base_lit) (k:nat) s (m':gmap nat (nat * nat)),
          l ↪ urn_unif s ∗ ⌜set_Forall (λ x, (0<=x<p)%Z) s⌝ ∗
          arr ↦ (#k, #lm)%V ∗
          ⌜2<=k<=tries + 2⌝ ∗
          ltries ↦ #(tries +2 -k)%nat ∗
          map_list lm ((λ x, #x) <$> m) ∗
          ⌜dom m = set_seq 0 k⌝ ∗
          ⌜map_Forall (λ _ x, base_lit_type_check x = Some BLTInt) m⌝ ∗
          ⌜is_valid_urn (urn_unif s)⌝ ∗
          mono_nat_auth_own γ2 1 (k-1) ∗
          ⌜dom m = dom m'⌝ ∗ 
          ⌜map_Forall (λ _ x, 0<=x.1<p/\0<=x.2<p) m'⌝ ∗
          ⌜map_match m m' l⌝  ∗
          (⌜map_no_coll m' s⌝ ∗
           ⌜p<=size s+k*(k-1)/2⌝ ∗
           ↯ ((1+(tries+2-k)*(tries+k+1)%nat/2)/(size s))
           ∨
             token γ1
          )
      )%I.

    Lemma value_in_interp lm arr ltries l γ γ':
      mono_nat_lb_own γ' 1 -∗
      inv nroot (dlog_inv lm arr ltries l γ γ') -∗
      (∃ τ, τ * τ * (τ → τ → () + τ) * (τ → () + τ) * (τ → τ → lrel_bool))%lrel
        (#0%nat, #1%nat, group_mul_specialized #arr (try_spend_specialized #ltries),
           group_inv_specialized #arr (try_spend_specialized #ltries),
             group_eq_specialized (#arr))%V.
    Proof.
      iIntros "#Hfrag #Hinv".
      iExists (LRel (λ x, ∃ (n:nat), ⌜ x= #n⌝  ∗ mono_nat_lb_own γ' n)%I).
      repeat (iExists _, _; iSplit; first done; iSplit).
      - (* 0 *)
        iExists 0%nat.
        iSplit; first done.
        iApply (mono_nat_lb_own_le); last done.
        lia.
      - (* 1 *)
        iExists 1%nat.
        by iSplit. 
      - (* mult *)
        iIntros (h1).
        iModIntro.
        iIntros "(%n1&->&#Hfrag1)".
        rewrite refines_eq /refines_def.
        rewrite /group_mul_specialized.
        wp_pures.
        iModIntro.
        iIntros (h2).
        iModIntro.
        iIntros "(%n2&->&#Hfrag2)".
        rewrite refines_eq /refines_def.
        wp_pures.
        iInv "Hinv" as ">(%m&%k&%s'&%m'&Hurn&%Hs&Harr&%&Htries&Hm&%Hdom&%Hforall&%&Hauth&%Hdom'&%Hforall2&%Hmatch&Hor)" "Hclose".
        rewrite /try_spend_specialized.
        wp_pures.
        wp_load.
        wp_pures.
        case_bool_decide.
        { wp_pures.
          iMod ("Hclose" with "[-]"); first by iFrame.
          iExists _. iLeft.
          iPureIntro. naive_solver.
        }
        wp_pures.
        wp_store.
        wp_pures.

        
        iDestruct (mono_nat_lb_own_valid with "[$][$Hfrag1]") as "%".
        iDestruct (mono_nat_lb_own_valid with "[$][$Hfrag2]") as "%".
        assert (n1 ∈ dom m) as Hlookup1.
        { rewrite Hdom. rewrite elem_of_set_seq. destruct!/=; simpl in *.
          lia. }
        pose proof Hlookup1 as Hlookup1'.
        rewrite elem_of_dom in Hlookup1.
        destruct Hlookup1 as [x1 Hlookup1].
        assert (n2 ∈ dom m) as Hlookup2.
        { rewrite Hdom. rewrite elem_of_set_seq. destruct!/=; simpl in *.
          lia. }
        
        pose proof Hlookup2 as Hlookup2'.
        rewrite elem_of_dom in Hlookup2.
        destruct Hlookup2 as [x2 Hlookup2].
        
        rewrite /arr_get.
        wp_pures.
        wp_load.
        wp_pures.
        wp_apply (wp_get with "[$]").
        iIntros (?) "(Hm & ->)".
        simplify_map_eq.
        wp_pures.
        wp_load.
        wp_pures.
        wp_apply (wp_get with "[$]").
        iIntros (?) "(Hm & ->)".
        simplify_map_eq.
        wp_pures.

        iMod (mono_nat_own_update k with "[$]") as "[Hauth #Hfrag']"; first lia.
        

        apply Hforall in Hlookup1 as Htype1.
        apply Hforall in Hlookup2 as Htype2.
        rewrite /arr_push.
        rewrite Hdom' in Hlookup1'.
        rewrite Hdom' in Hlookup2'.
        rewrite elem_of_dom in Hlookup1'.
        rewrite elem_of_dom in Hlookup2'.
        destruct Hlookup1' as [[a b] Hlookup1'].
        destruct Hlookup2' as [[a' b'] Hlookup2'].
        eapply Hmatch in Hlookup1' as Hmatch1; last done.
        eapply Hmatch in Hlookup2' as Hmatch2; last done.
        
        assert (∃ (x3:base_lit), bin_op_eval PlusOp #x1 #x2 = Some #x3 /\
                          base_lit_type_check x3 = Some BLTInt /\
                          (∀ f x, (0<=x<p)%Z -> f!!l=Some x->
                                  urn_subst f x3 =
                                  Some (LitInt ((a * x + b) `mod` p + (a' * x + b') `mod` p)%Z)
                          )
               ) as (x3 & ?&Htype3&Hmatch3).
        {
          destruct (is_simple_base_lit x1) eqn:?; last first.
          - exists (x1 +ᵥ x2)%V.
            simpl. rewrite Htype1 Htype2.
            split; last (split; first done); first by case_match.
            intros.
            erewrite Hmatch1; try done. 
            by erewrite Hmatch2.
          - destruct (is_simple_base_lit x2) eqn:?; last first.
            + exists (x1 +ᵥ x2)%V.
              simpl. rewrite Htype1 Htype2.
              split; last (split; first done).
              * case_match; try done; by case_match.
              * intros. erewrite Hmatch1; try done.
                by erewrite Hmatch2.
            + destruct x1, x2; try done; naive_solver.
        }
        wp_pure.
        rewrite /zmod.
        wp_pures.
        assert (∃ (x4:base_lit), bin_op_eval RemOp #x3 #p = Some #x4 /\
                          base_lit_type_check x4 = Some BLTInt /\
                          (∀ f x, (0<=x<p)%Z -> f!!l=Some x->
                                  urn_subst f x4 =
                                  Some (LitInt (((a * x + b) `mod` p + (a' * x + b') `mod` p) `rem` p)%Z)
                          )
               ) as (x4 & ?&Htype4&Hmatch4).
        {
          destruct (is_simple_base_lit x3) eqn:?; last first.
          - exists (RemOp' x3 p)%V.
            simpl. rewrite Htype3.
            split; last (split; first done); first by case_match.
            intros.
            by erewrite Hmatch3.
          - destruct x3; try done; naive_solver.
        }
        assert (∀ (f : gmap loc Z) (x : Z),
                  (0 ≤ x < p)%Z
                  → f !! l = Some x
                  → urn_subst f x4 =
                  Some (LitInt((((a+a') `mod` p)%nat * x + ((b+b') `mod` p)%nat)`mod`p)%Z)) as Hmatch4'.
        {
          intros. erewrite Hmatch4; try done.
          destruct Hprime.
          f_equal. 
          f_equal.
          rewrite Z.rem_mod_nonneg; last (lia); last first.
          - apply Z.add_nonneg_nonneg;
              apply Z.mod_pos; lia.
          - rewrite -Zplus_mod.
            replace (_+(_*_+_))%Z with ((a+a')*x+(b+b'))%Z by lia.
            rewrite Zplus_mod.
            rewrite Zmult_mod.
            rewrite Zmult_mod_idemp_r.
            rewrite Zplus_mod_idemp_l.
            rewrite !Nat2Z.inj_mod. lia.
        }
        
        wp_pures.
        wp_load.
        wp_pures.
        wp_apply (wp_set with "[$]").
        iIntros "Hm".
        wp_store.
        rewrite -fmap_insert.

        iDestruct ("Hor") as "[(%Hcoll&%Hsize&Herr)|Htoken]"; last first.
        {
          wp_pures.
          iMod ("Hclose" with "[-]"); last first.
          - iExists _. iRight.
            iModIntro. iSplit; first done.
            iExists k; by iSplit.
          - iFrame.
            iExists (k+1).
            replace ((_+_-_)%nat-_)%Z with (Z.of_nat (tries + 2 - (k+1))%nat)%Z by lia.
            replace (k+1)%Z with (Z.of_nat (k+1)) by lia.
            iFrame.
            replace (_+_-_) with k by lia.
            iFrame.
            iNext.
            iExists (<[k:=((a+a') mod p, (b+b') mod p)]> m').
            repeat iSplit; iPureIntro.
            + done.
            + lia.
            + lia.
            + rewrite dom_insert_L.
              rewrite Hdom.
              replace (_+_) with (S k) by lia.
              rewrite set_seq_S_end_union_L.
              f_equal.
            + intros ?? Hlookup.
              apply lookup_insert_Some in Hlookup.
              destruct!/=; first done.
              naive_solver.
            + done.
            + by rewrite !dom_insert_L Hdom'.
            + intros ?? Hlookup.
              apply lookup_insert_Some in Hlookup.
              destruct!/=.
              * split.
                -- apply Nat.mod_bound_pos; destruct Hprime; lia.
                -- apply Nat.mod_bound_pos; destruct Hprime; lia.
              * by eapply Hforall2.
            + intros k' ??? Hlookupa Hlookupb ??? Hf. 
              destruct (decide (k=k')).
              * subst. simplify_map_eq.
                by erewrite Hmatch4'.
              * simplify_map_eq. naive_solver.
        }

        assert (0<size s').
        { destruct (size s') eqn:Hcontra; last lia.
          exfalso.
          apply size_empty_iff in Hcontra. set_solver.  }

        (* rewrite err *)
        iDestruct (ec_eq _
                     (((1 + ((tries)%nat + 2 - (k+1)%nat) * ((tries)%nat + (k+1)%nat + 1)%nat / 2) + (INR k))/size s') with "[$]") as "Herr".
        { f_equal.
          rewrite Rplus_assoc. f_equal.
          rewrite !plus_INR.
          simpl. lra.
        }
        destruct (decide (k<size s')); last first. 
        {
          iDestruct (ec_contradict with "[$]") as "[]".
          trans (k/size s')%R.
          - apply Rcomplements.Rle_div_r.
            + apply Rlt_gt.
              by apply lt_0_INR.
            + rewrite Rmult_1_l. apply le_INR. lia.
          - rewrite Rdiv_plus_distr.
            rewrite (Rplus_comm _ (_/_)%R). apply Rplus_le_0_compat.
            apply Rcomplements.Rdiv_le_0_compat; last (apply lt_0_INR; lia).
            apply Rplus_le_le_0_compat; first lra.
            apply Rcomplements.Rdiv_le_0_compat; last lra.
            replace 2%R with (INR 2) by done.
            rewrite -plus_INR -minus_INR; last lia.
            rewrite -mult_INR. real_solver. 
        }
        iMod (pupd_reduce_urn_list m' ((a+a') `mod` p) ((b+b') `mod` p) with "[$][$]") as "Hres".
        { rewrite -size_dom. rewrite -Hdom' Hdom.
          by rewrite size_set_seq. 
        }
        { done. }
        { apply Rplus_le_le_0_compat; first lra.
          apply Rcomplements.Rdiv_le_0_compat; last lra.
          replace 2%R with (INR 2) by done.
          rewrite -plus_INR -minus_INR; last lia.
          rewrite -mult_INR. real_solver.  }
        { apply Nat.mod_bound_pos; try lia. destruct Hprime. lia. }
        { apply Nat.mod_bound_pos; try lia. destruct Hprime. lia. }
        { done. }
        { done. }
        iDestruct "Hres" as "(%s''&%&%&%Hcoll'&Hurn&Herr)".
        wp_pures.
        iMod ("Hclose" with "[-]"); last first.
        { iExists _.
          iModIntro. iRight.
          iSplit; first done.
          iExists _; by iSplit. 
        }
        iNext.
        rewrite /dlog_inv.
        iFrame.
        iExists (k+1), (<[k:= (((a+a')`mod`p), ((b+b')`mod`p))]>m').
        replace (Z.of_nat _ + 1)%Z with (Z.of_nat (k+1)) by lia.
        replace (Z.of_nat _ - _)%Z with (Z.of_nat (tries+2 - (k+1)%nat)) by lia.
        replace (_+_-1) with k by lia.
        iFrame. 
        repeat iSplit; last iLeft; last iFrame "Herr"; repeat iSplit; iPureIntro. 
        + intros ?. intros. apply Hs. set_solver.
        + lia.
        + lia.
        + rewrite dom_insert_L.
          replace (k+1) with (S k) by lia.
          rewrite set_seq_S_end_union_L. simpl.
          set_solver.
        + by apply map_Forall_insert_2.
        + simpl. assert (0≠size s'') as Hcontra by lia.
          intros ->.
          by rewrite size_empty in Hcontra.
        + rewrite !dom_insert_L. set_solver.
        + apply map_Forall_insert_2; last done.
          simpl.
          split.
          * apply Nat.mod_bound_pos; destruct Hprime; lia.
          * apply Nat.mod_bound_pos; destruct Hprime; lia.
        + intros k'?????.
          destruct (decide (k=k')); subst.
          * simplify_map_eq.
            intros. by erewrite Hmatch4'.
          * simplify_map_eq. naive_solver.
        + intros k1 k2 ??????.
          destruct (decide (k=k1)); destruct (decide(k=k2)); subst; simplify_map_eq.
          * intros ??. naive_solver.
          * by eapply Hcoll'.
          * apply no_coll_swap.
            by eapply Hcoll'.
          * intros ???.
            eapply Hcoll; try done.
            set_solver.
        + etrans; first exact.
          replace (_.1) with ((k*(k-1)) `div` 2) by done.
          trans (size s'' + k+   (k * (k - 1)) `div` 2); first lia.
          assert ( k + (k * (k - 1)) `div` 2 ≤  ((k + 1) * k) `div` 2); last lia.
          rewrite -Nat.div_add_l; last lia.
          apply Nat.Div0.div_le_mono.
          lia.
      - (* inv *)
        iIntros (h).
        iModIntro.
        iIntros "(%n&->&#Hfrag')".
        rewrite refines_eq /refines_def.
        rewrite /group_inv_specialized.
        wp_pures.
        admit. 
      - (* eq *)
        iIntros (h1).
        iModIntro.
        iIntros "(%n1&->&#Hfrag1)".
        rewrite refines_eq /refines_def.
        rewrite /group_eq_specialized.
        wp_pures.
        iModIntro.
        iIntros (h2).
        iModIntro.
        iIntros "(%n2&->&#Hfrag2)".
        rewrite refines_eq /refines_def.
        wp_pures.
        admit. 
    Admitted. 
    
    
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

    assert (size ((list_to_set (Z.of_nat <$> seq 0 p) ∖ {[1%Z]}):gset _) = p-1) as Hrewrite.
    { rewrite size_difference; last first.
      - set_unfold.
        intros. eexists 1; split; first done.
        rewrite elem_of_seq. lia.
      - rewrite size_singleton.
        rewrite size_list_to_set.
        + rewrite length_fmap length_seq. lia.
        + apply NoDup_fmap.
          * intros ???. by simplify_eq.
          * apply NoDup_seq. }
    (* Allocating invariant *)
    iMod (inv_alloc (nroot) _
            (dlog_inv _ _ _ _ γ γ')
           with "[-HΦ Htoken]") as "#Hinv".
    { iNext. rewrite /dlog_inv.
      iFrame "Hurn".
      iExists (<[1:=LitLbl l]> (<[0:=LitInt 1]> ∅)).
      iExists 2.
      replace (_+_-_)%nat with tries by lia.
      iFrame.
      iExists (<[1:=(1,0)]> (<[0:=(0,1)]> ∅)).
      repeat iSplit; last iLeft; repeat iSplit.
      - iPureIntro.
        intros ?. rewrite elem_of_difference.
        rewrite elem_of_list_to_set.
        rewrite elem_of_list_fmap.
        setoid_rewrite elem_of_seq. intros. destruct!/=. lia.
      - iPureIntro; lia.
      - iPureIntro.
        simpl. lia.
      - iPureIntro; by vm_compute.
      - iPureIntro.
        intros ?? Hlookup.
        apply lookup_insert_Some in Hlookup as [|[? Hlookup]];
        destruct!/=; first done.
        apply lookup_insert_Some in Hlookup; by destruct!/=.
      - iPureIntro.
        simpl.
        intros Hcontra.
        apply (f_equal size) in Hcontra.
        rewrite Hrewrite in Hcontra.
        rewrite size_empty in Hcontra; lia.
      - iPureIntro. by vm_compute.
      - iPureIntro.
        intros ?? Hlookup.
        apply lookup_insert_Some in Hlookup as [|[? Hlookup]]; destruct!/=; first lia.
        apply lookup_insert_Some in Hlookup as [|[? Hlookup]]; destruct!/=; lia.
      - iPureIntro.
        rewrite /map_match.
        intros k?????.
        intros.
        destruct k as [|[|]]; simplify_map_eq.
        + replace (_*_+_)%Z with 1%Z by lia.
          rewrite Zmod_small; first done. lia.
        + replace (_*_+_)%Z with x by lia.
          rewrite Zmod_small; first done. lia.
      - iPureIntro.
        intros [|[|]] [|[|]]??????; simplify_map_eq.
        + intros ??; destruct!/=.
        + intros ? _.
          rewrite elem_of_difference.
          rewrite elem_of_list_to_set.
          rewrite elem_of_list_fmap.
          setoid_rewrite elem_of_seq.
          intros [[y]].
          destruct!/=.
          replace (_*_+1%nat)%Z with 1%Z by lia.
          replace (_*_+_)%Z with (Z.of_nat y) by lia.
          rewrite Zmod_small; last lia.
          rewrite Zmod_small; last lia.
          intros ?. set_solver.
        + intros ? _. rewrite elem_of_difference.
          rewrite elem_of_list_to_set.
          rewrite elem_of_list_fmap.
          setoid_rewrite elem_of_seq.
          intros [[y]].
          destruct!/=.
          replace (_*_+1%nat)%Z with 1%Z by lia.
          replace (_*_+_)%Z with (Z.of_nat y) by lia.
          rewrite Zmod_small; last lia.
          rewrite Zmod_small; last lia.
          intros ?. set_solver.
        + intros ??; destruct!/=.
      - iPureIntro.
        simpl.
        rewrite Hrewrite. lia.
      - iApply (ec_eq with "[$]").
        simpl. f_equal; last by rewrite Hrewrite.
        repeat f_equal; try lra.
        rewrite !plus_INR. simpl. lra.
    }
    
    wp_bind (v _)%E.
    rewrite refines_eq /refines_def.
    simpl.
    iApply (pgl_wp_wand); first iApply "Hinterp"; first by iApply value_in_interp.
    iIntros (?) "[%guess ->]".
    do 2 wp_pure.
    rewrite -(fill_empty (_=_)).
    iApply pgl_wp_bind.
    simpl.
    wp_pures.
    iInv "Hinv" as ">(%m&%k&%s'&%m'&Hurn&%&Harr&%&Htries&Hm&%&%&%&Hauth&%&%&%&[(%&%&Herr)|Htoken'])" "Hclose"; last iDestruct (token_exclusive with "[$][$]") as "[]".
    iDestruct (ec_weaken _ (1/size s') with "[$]") as "Herr".
    { split; first apply Rdiv_INR_ge_0.
      rewrite !Rdiv_def.
      apply Rmult_le_compat_r; first (rewrite -Rdiv_1_l; apply Rdiv_INR_ge_0).
      apply Rplus_le_0_compat.
      repeat apply Rmult_le_pos; try lra.
      - assert (k<=tries +2)%R; last lra.
        replace 2%R with (INR 2) by done.
        rewrite -plus_INR.
        apply le_INR. lia.
      - real_solver.
    }
    destruct (decide (Z.of_nat guess ∈ s')).
    - (* guess in s *)
      iMod (pupd_resolve_urn _ _ (λ x, if bool_decide (x=Z.of_nat guess) then nnreal_one else nnreal_zero) with "[$][$]") as "(%&?&Hurn&%)".
      + done.
      + erewrite (SeriesC_ext _ (λ x, if bool_decide (x=Z.of_nat guess) then nnreal_one else nnreal_zero)); last first.
        * intros.
          case_bool_decide as K1; first by case_bool_decide.
          rewrite bool_decide_eq_false_2; first done.
          intros ->. apply K1. set_solver.
        * rewrite SeriesC_singleton.
          simpl.
          rewrite !Rdiv_def.
          apply Rmult_le_compat_r.
          -- rewrite -Rdiv_1_l.
             apply Rdiv_INR_ge_0.
          -- replace 1%R with (INR 1) by done.
             apply le_INR.
             lia.      
      + exists 1.
        intros.
        case_bool_decide; simpl; lra.
      + case_bool_decide; first by iDestruct (ec_contradict with "[$]") as "[]".
        iApply (wp_value_promotion _ false (l↪ _) with "[Hurn]").
        * rewrite rupd_unseal/rupd_def.
          iIntros  (?) "[? Hu]". iSplit; last iFrame.
          iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
          iPureIntro.
          intros.
          eapply urns_f_distr_lookup in Hlookup; last done; last done.
          destruct Hlookup as (?&Hsome&Hin).
          simpl.
          rewrite Hsome.
          simpl.
          rewrite bool_decide_eq_false_2; first naive_solver.
          set_unfold.
          destruct!/=. intros ?. simplify_eq.
        * iIntros "Hurn".
          wp_pures.
          iMod ("Hclose" with "[-HΦ]").
          { iNext.
            iFrame.
            iExists _. repeat iSplit; try done.
            - iPureIntro.
              intros ??. set_unfold. naive_solver.
            - iPureIntro. lia.
            - iPureIntro. lia.
          }
          by iApply "HΦ".
    - (* guess not in s *)
      iMod (pupd_resolve_urn _ _ (λ x, nnreal_zero) with "[$][$]") as "(%&?&Hurn&%)".
      + done.
      + rewrite SeriesC_list_2; last apply NoDup_elements.
        simpl.
        replace (_*_/_)%R with 0%R by lra.
        apply Rdiv_INR_ge_0.
      + naive_solver. 
      + iApply (wp_value_promotion _ false (l↪ _) with "[Hurn]").
        * rewrite rupd_unseal/rupd_def.
          iIntros  (?) "[? Hu]". iSplit; last iFrame.
          iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
          iPureIntro.
          intros.
          eapply urns_f_distr_lookup in Hlookup; last done; last done.
          destruct Hlookup as (?&Hsome&Hin).
          simpl.
          rewrite Hsome.
          simpl.
          rewrite bool_decide_eq_false_2; first naive_solver.
          set_unfold.
          destruct!/=. intros ?. simplify_eq.
        * iIntros "Hurn".
          wp_pures.
          iMod ("Hclose" with "[-HΦ]").
          { iNext.
            iFrame.
            iExists _. repeat iSplit; try done.
            - iPureIntro.
              intros ??. set_unfold. naive_solver.
            - iPureIntro. lia.
            - iPureIntro. lia.
          }
          by iApply "HΦ".
  Qed. 

End prog.

  (* rewrite rupd_unseal/rupd_def. *)
  (* iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
  (* iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
  (* iPureIntro. *)
  (* intros. *)
  (* eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
  (* destruct Hlookup as (?&Hsome&Hin). *)
  (* simpl.  *)


  
  (* destruct (decide (is_simple_base_lit x1 =true /\ is_simple_base_lit x2 = true)) as [[Hcase Hcase']|Hcase]. *)
  (* + (* values are both simple *) *)
  (*   destruct x1; simplify_eq.  *)
  (*   destruct x2; simplify_eq. *)
  (*   wp_pures. *)
  (*   rewrite /zmod. *)
  (*   wp_pures. *)
  (*   wp_load. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_set with "[$]"). *)
  (*   iIntros "Hm". *)
  (*   wp_pures. *)
  (*   wp_store. *)
  (*   rewrite -fmap_insert. *)
  (*   rewrite Hdom' in Hlookup1'. *)
  (*   rewrite Hdom' in Hlookup2'. *)
  (*   rewrite elem_of_dom in Hlookup1'. *)
  (*   rewrite elem_of_dom in Hlookup2'. *)
  (*   destruct Hlookup1' as [[a b] Hlookup1']. *)
  (*   destruct Hlookup2' as [[a' b'] Hlookup2']. *)

  (*   (* split the or *) *)
  (*   iDestruct "Hor" as "[(%Hcoll&%Hineq&Herr)|Htoken]"; last first. *)
  (*   { *)
  (*     wp_pures. *)
  (*     iMod ("Hclose" with "[-]"); last first. *)
  (*     - iExists _. iRight. *)
  (*       iModIntro. iSplit; first done. *)
  (*       iExists k; by iSplit. *)
  (*     - iFrame. *)
  (*       iExists (k+1). *)
  (*       replace ((_+_-_)%nat-_)%Z with (Z.of_nat (tries + 2 - (k+1))%nat)%Z by lia. *)
  (*       replace (k+1)%Z with (Z.of_nat (k+1)) by lia. *)
  (*       iFrame.  *)
  (*       replace (_+_-_) with k by lia. *)
  (*       iFrame. *)
  (*       iNext. *)
  (*       iExists (<[k:=((a+a') mod p, (b+b') mod p)]> m'). *)
  (*       repeat iSplit; iPureIntro. *)
  (*       + done. *)
  (*       + lia. *)
  (*       + lia. *)
  (*       + rewrite dom_insert_L. *)
  (*         rewrite Hdom. *)
  (*         replace (_+_) with (S k) by lia. *)
  (*         rewrite set_seq_S_end_union_L. *)
  (*         f_equal.  *)
  (*       + intros ?? Hlookup. *)
  (*         apply lookup_insert_Some in Hlookup. *)
  (*         destruct!/=; first done. *)
  (*         naive_solver. *)
  (*       + done. *)
  (*       + by rewrite !dom_insert_L Hdom'.  *)
  (*       + intros ?? Hlookup. *)
  (*         apply lookup_insert_Some in Hlookup. *)
  (*         destruct!/=. *)
  (*         * split. *)
  (*           -- apply Nat.mod_bound_pos; destruct Hprime; lia. *)
  (*           -- apply Nat.mod_bound_pos; destruct Hprime; lia. *)
  (*         * by eapply Hforall2. *)
  (*       + intros k' ????? Hlookupa Hlookupb ? Hf. *)
  (*         destruct (decide (k=k')). *)
  (*         * subst. simplify_map_eq. *)
  (*           f_equal.  *)
  (*           eapply Hmatch in Hlookup1'. *)
  (*           apply Hlookup' in Hlookup1'. *)
  (*           admit. *)
  (*         * simplify_map_eq. naive_solver. *)
  (*   } *)
