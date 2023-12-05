(* A case study of coupon collection *)
From clutch Require Export clutch.
From clutch.lib Require Export map.

Set Default Proof Using "Type*".


Definition cnt_map_helper : expr :=
    (rec: "cnt_helper" "m" "k" "n" :=
       if: "k" = "n"
       then #0
       else
         match: get "m" "k" with
           NONE => "cnt_helper" "m" ("k"+#1) 
         | SOME <> =>
             #1 + "cnt_helper" "m" ("k"+#1)
         end
    ).

  Definition cnt_map : expr:=
    λ: "m" "n",
      cnt_map_helper "m" #0 "n".
      
  Definition coupon_helper : expr :=
    rec: "coupon_helper" "m" "n" "cnt" :=
      if: cnt_map "m" "n" = "n" then !"cnt" else
        "cnt" <- !"cnt" + #1;;
        let: "k" := rand ("n" - #1) from #() in
        set "m" "k" #();;
        "coupon_helper" "m" "n" "cnt".
        
  Definition coupon_collection : expr :=
    λ: "n",
      let: "m" := init_map #() in
      let: "cnt" := ref #0 in
      coupon_helper "m" "n" "cnt". 

  Definition spec_coupon_helper : expr :=
    rec: "spec_coupon_helper" "t" "n" "cnt" :=
      if: "n" = "t" then !"cnt" else
        "cnt" <- !"cnt" + #1;;
        let: "k" := rand ("n" - #1) from #() in
        if: ("t" ≤ "k") then "spec_coupon_helper" ("t"+#1) "n" "cnt"
        else "spec_coupon_helper" "t" "n" "cnt".
  
  Definition spec_coupon_collection : expr :=
    λ: "n",
      let: "t" := #0 in
      let: "cnt" := ref #0 in
      spec_coupon_helper "t" "n" "cnt".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition couponN := nroot.@"coupon".

  (**  TODO! *)
  Fixpoint cnt_gallina (vs: gmap nat val) (k:Z) (n:nat) := Z.of_nat 0.

  (* This is an invariant in the sense that it holds true for every recursive call, 
     but we do not technically allocate it as an invariant in the RA sense. 
   *)
  Definition coupon_collection_inv n m (k:Z) cnt cnt':= (∃(cntv : Z) lis , map_list m lis ∗ cnt' ↦ₛ #cntv ∗ cnt ↦ #cntv ∗ ⌜cnt_gallina lis 0 n = k⌝ )%I.

  Lemma coupon_collection_refines_spec_helper n m (k:Z) cnt cnt':
    ⊢ coupon_collection_inv n m k cnt cnt' -∗ REL coupon_helper #m #n #cnt << spec_coupon_helper #k #n #cnt' : lrel_nat.
  Proof.
    iLöb as "IH" forall (k).
    iIntros "Inv".
    iDestruct "Inv" as (??) "(?&?&?&%)".
    rewrite {2}/coupon_helper {2}/spec_coupon_helper.
    do 10 rel_pure_l. 
    rewrite -!/cnt_map_helper.
    rel_pures_r.
    case_bool_decide.
    - (* finish collecting*)
      rel_pures_r. rel_load_r.
      subst. 
      inversion H0; subst. 
      rel_apply_l (refines_wp_l _ _ (cnt_map_helper _ _ _)).
    Admitted. 
  
  Lemma coupon_collection_refines_spec:
    ⊢ REL coupon_collection << spec_coupon_collection : lrel_nat → lrel_nat.
  Proof.
    rel_arrow_val. iIntros (v1 v2 [n[-> ->]]) .
    rel_pures_l.
    rel_pures_r.
    rel_alloc_r cnt' as "Hcnt'". do 2 rel_pure_r.
    rel_apply_l (refines_wp_l _ _ (init_map #())).
    wp_apply (wp_init_map with "[//]").
    iIntros (m) "Hm".
    rel_pures_l.
    rel_alloc_l cnt as "Hcnt".
    do 2 rel_pure_l.
    rewrite -/coupon_helper -/spec_coupon_helper.
    iApply (coupon_collection_refines_spec_helper with "[Hcnt' Hm Hcnt]").
    rewrite /coupon_collection_inv; iExists _, _. iFrame.
    by iPureIntro. 
Qed. 

  
  
  
  
End proofs.
