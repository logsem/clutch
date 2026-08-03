From clutch.prob_eff_lang.probblaze Require Import semantics syntax notation logic proofmode spec_tactics.
From clutch.prob_eff_lang.probblaze.typing Require Import types.

#[warning="-hiding-delimiting-key,-overwriting-delimiting-key -notation-incompatible-prefix"]
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool zmodp.

From clutch.prelude Require Import mc_stdlib.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup.
From clutch.approxis Require Import app_weakestpre.

Local Open Scope group_scope.
Import fingroup.fingroup.
Import finalg.FinRing.Theory.
Set Default Proof Using "Type*".
Set Bullet Behavior "Strict Subproofs".

Section Zpx.

  Import finalg.
  Context (p''' : nat).
  Notation p'' := (S p''').
  Notation p := (S (S p'')).

  #[local] Definition cval := syntax.val.
  Definition Zpx : finGroupType := FinGroup.clone _ {unit 'Z_p}.

  Definition vgval_p (n : Zpx) : cval := #(Z.of_nat (nat_of_ord (FinRing.uval n))).

  Local Instance vgval_inj_p : Inj eq eq vgval_p.
  Proof.
    intros x y h. inversion h as [hh]. apply val_inj.
    destruct x as [x hx], y as [y hy] ; simpl in *.
    apply Nat2Z.inj, ord_inj in hh. exact hh.
  Qed.

  Instance vg_p : val_group :=
    {| vgG := Zpx
    ; vgval := vgval_p
    ; vgval_inj := vgval_inj_p |}.

  Import valgroup_notation.

  Definition vunit_p : cval := vgval (1%g : vgG).
  Lemma vunit_p_typed : ⊢ᵥ vunit_p : ℤ. 
  Proof. apply Int_val_typed. Qed.
  Lemma is_unit_p : vunit_p = vgval_p 1. 
  Proof. done. Qed.
  Definition vmult_p := (λ:"a" "b", ("a" * "b") `rem` #p)%V.
  Lemma vmult_p_typed : ⊢ᵥ vmult_p : (ℤ ⇾ ℤ ⇾ ℤ).
  Proof. 
    apply Rec_val_typed; first done.
    simpl. rewrite -(app_nil_r [:: _]).
    eapply (Rec_typed _ _ ∅); [done
                              |rewrite /ctx_dom //=; set_solver
                              |rewrite /ctx_dom //=
                              |apply Forall_singleton; constructor
                              |simpl].
    eapply BinOp_typed; [constructor
                        |
                        |apply Val_typed; constructor].

    eapply BinOp_typed; first constructor; apply Var_typed.
  Qed. 
  Definition vinv_p := (λ:"x", (vexp' vunit_p vmult_p "x" (#p'')) `rem` #p)%V.
  Lemma vinv_p_typed : ⊢ᵥ vinv_p : (ℤ ⇾ ℤ).
  Proof. 
    constructor; first done.
    eapply BinOp_typed; [constructor| | apply Val_typed; constructor].
    eapply App_typed; [constructor
                      |constructor
                      |constructor;exists true;constructor
                      |constructor
                      |apply Val_typed;constructor
                      |].
    eapply Sub_typed; [apply CRefl_le
                      |apply CRefl_le
                      |apply RRefl_le
                      |eapply (le.TBangElim_le _ MS)
                      | ].
    eapply App_typed; [constructor
                      |constructor
                      |constructor;exists true;constructor
                      |constructor
                      |apply Weakening_typed; apply Var_typed
                      |].
    eapply Sub_typed; [apply CRefl_le
                      |apply CRefl_le
                      |apply RRefl_le
                      |eapply (le.TBangElim_le _ MS)
                      | ].
    apply Val_typed.
    eapply Rec_val_typed; first done. simpl.
    rewrite -(app_nil_r [:: _]).
    eapply (Rec_typed _ _ ∅); [done
                              |rewrite /ctx_dom //=
                              |rewrite /ctx_dom //=
                              |apply Forall_singleton; constructor
                              |].
    eapply If_typed.
    { eapply BinOp_typed; first constructor.
      2 : { apply Val_typed; constructor. }
      eapply Sub_typed; [eapply _ctx_perm_right; first apply CRefl_le; apply perm_swap
                        |apply CRefl_le
                        |apply RRefl_le
                        |constructor
                        |].
      eassert (<["n" :=c ℤ%ty]> [:: ("vexp", _); ("a", _)] =  [:: ("n", ℤ%ty); ("vexp", (ℤ ⇾ ℤ)%ty); ("a", ℤ%ty)]) as <- by done.
      apply Contraction_typed; first constructor.
      apply Var_typed. }
    { eapply (Sub_typed _ _ ∅); [done
                                |apply CRefl_le
                                |apply RRefl_le
                                |constructor
                                |].
      apply Val_typed. 
      apply vunit_p_typed. }
    eapply App_typed; [constructor
                      |constructor
                      |constructor;exists true;constructor
                      |constructor
                      |
                      |].
    { eapply (App_typed _ _ _ (<["a" :=c ℤ%ty]> ∅)); [constructor
                                                     |constructor
                                                     |constructor;exists true;constructor
                                                     |constructor;constructor;exists true;constructor
                                                     |
                                                     |].
      1 : { eapply BinOp_typed; first constructor; last first.
            - apply Val_typed; constructor.
            - apply Var_typed. }
      eassert (<["vexp" :=c _]> [:: ("a", _)] =  [:: ("vexp",_); ("a", _)]) as <- by done.      
      eapply Sub_typed; [apply CRefl_le
                        |apply CRefl_le
                        |apply RRefl_le
                        |eapply (le.TBangElim_le _ MS)
                        |apply Var_typed]. }
    eapply Sub_typed; [apply CRefl_le
                      |apply CRefl_le
                      |apply RRefl_le
                      |eapply (le.TBangElim_le _ MS)
                      |].
    simpl. rewrite -(app_nil_r [:: _]).
    eapply (Rec_typed _ _ ∅); [done
                              |rewrite /ctx_dom //=; set_solver
                              |rewrite /ctx_dom //=
                              |apply Forall_singleton; constructor
                              |simpl].
    eapply App_typed; [constructor
                      |constructor
                      |constructor;exists true;constructor
                      |constructor
                      |apply Var_typed
                      |].
    eapply Sub_typed; [apply CRefl_le
                      |apply CRefl_le
                      |apply RRefl_le
                      |eapply (le.TBangElim_le _ MS)
                      |].
    eapply App_typed; [constructor
                      |constructor
                      |constructor;exists true;constructor
                      |constructor
                      |apply Var_typed
                      |]. 
    eapply Sub_typed; [apply CRefl_le
                      |apply CRefl_le
                      |apply RRefl_le
                      |eapply (le.TBangElim_le _ MS)
                      |].
    apply Val_typed.
    apply vmult_p_typed. Unshelve. all: exact true.
  Qed. 
  Definition veq_p := (λ:"x" "y", "x" = "y")%V.
  Lemma veq_p_typed : ⊢ᵥ veq_p : (ℤ ⇾ ℤ ⇾ 𝔹). 
  Proof.
    apply Rec_val_typed; first done.
    simpl. rewrite -(app_nil_r [:: _]).
    eapply (Rec_typed _ _ ∅); [done
                              |rewrite /ctx_dom //=; set_solver
                              |rewrite /ctx_dom //=
                              |apply Forall_singleton; constructor
                              |simpl].
    eapply BinOp_typed; first constructor; apply Var_typed.
  Qed. 
  Definition int_of_vg_p := (λ:"a", "a")%V.
  Lemma int_of_vg_p_typed : ⊢ᵥ int_of_vg_p : (ℤ ⇾ ℤ). 
  Proof. apply Rec_val_typed; first done. apply Var_typed. Qed.
  Definition vg_of_int_p :=
    (λ:"a", if: (#1 ≤ "a") && ("a" < #p) then SOME "a" else NONE)%V.
  Lemma vg_of_int_p_typed :  ⊢ᵥ vg_of_int_p : (ℤ ⇾ () + ℤ).
  Proof. 
    apply Rec_val_typed; first done. 
    eapply If_typed.
    - rewrite /∅ /empty_ctx //=.
      eassert (<["a" :=c ℤ%ty]> [::] = [:: ("a", ℤ%ty)]) as <- by done.
      do 2 (apply Contraction_typed; first constructor).
      eapply If_typed.
      + eapply BinOp_typed;[constructor
                           |apply Val_typed; constructor
                           |apply Var_typed].
      + eapply BinOp_typed;[constructor
                           |apply Var_typed
                           |apply Val_typed; constructor].
      + apply Weakening_typed. apply Val_typed. constructor.
    - apply InjR_typed. apply Var_typed.
    - apply InjL_typed. apply Weakening_typed. apply Val_typed. constructor.
  Qed. 

  Instance cgs_p : clutch_group_struct.
  Proof using p'''.
    unshelve eapply ({|
          vunit := vunit_p ;
          vunit_typed := vunit_p_typed ;
          vinv := vinv_p ;
          vinv_typed := vinv_p_typed ;
          vmult := vmult_p ;
          vmult_typed := vmult_p_typed ;
          veq := veq_p ;
          veq_typed := veq_p_typed ;
          int_of_vg := int_of_vg_p ;
          int_of_vg_typed := int_of_vg_p_typed ;
          vg_of_int := vg_of_int_p ;
          vg_of_int_typed := vg_of_int_p_typed ;
          τG := TInt ;
        |}) .
    all: try set_solver.
    constructor.
  Defined.

  Context `{p_prime : is_true (prime.prime p)}.

  Definition vgg_p : val_group_generator (vg:=vg_p).
  Proof.
    move /cyclicP : (units_Zp_cyclic p_prime) => /= h.
    pose ((λ x, units_Zp p == cycle x) : ssrbool.pred {unit 'Z_p}) as P ; simpl in P.
    assert (zpgen : (∃ x, units_Zp p = cycle x) →
                    ∃ x, is_true (units_Zp p == cycle x)).
    { move => [/= x hx]. exists x. by apply /eqP. }
    destruct (sigW (zpgen h)) as [g hg].
    clear -hg p_prime ; simpl in *.
    unshelve econstructor.
    - exact g.
    - exact p'''.
    - done.
    - unfold order. move /eqP : hg => <-.
      rewrite card_units_Zp //=.
      apply prime.totient_prime => //.
    - rewrite /generator /=. unfold units_Zp in hg.
      apply Is_true_eq_left. by rewrite hg.
  Defined.

  (* Definition cgg_p : @clutch_group_generator vg_p cgs_p vgg_p.
     Proof.
       constructor. constructor.
     Defined. *)

  (* **************************************** *)
  (* Semantic conversion funcitons *)
  Lemma bound_is_a_unit : ∀ (n : Z), (1 ≤ n)%Z → (n < p)%Z
    → is_true ((inZp (Z.to_nat n)) \is a (@ssralg.GRing.unit ('Z_p : finUnitRingType))).
  Proof. rewrite /in_mem. simpl.
    rewrite /Zp_trunc. simpl.
    intros n Hnnonzero Hnbound.
    erewrite prime.prime_coprime.
    - rewrite /div.dvdn.
      rewrite div.modn_mod.
      rewrite div.modn_small.
      + Set Printing Coercions.
        rewrite -(Z2Nat.id n) in Hnbound; last lia. 
        apply Nat2Z.inj_lt in Hnbound.
        rewrite /is_true.
        apply negb_true_iff.
        apply (introF (@eqP _ _ _)).
        intro contra. lia.
      + rewrite -(Z2Nat.id n) in Hnbound; last lia.
        apply Nat2Z.inj_lt in Hnbound.
        apply (reflect_iff _ _ (@ssrnat.ltP _ _)) in Hnbound.
        apply Hnbound.
    - apply p_prime.
  Qed.
  
  Lemma bound_is_a_unit_Zp : ∀ (n : 'Z_p), (1 ≤ n)%Z
                                           → is_true (n \is a (@ssralg.GRing.unit ('Z_p : finUnitRingType))).
  Proof. intros n Hnnonzero.
         assert (eqnp : inZp (Z.to_nat (Z.of_nat (nat_of_ord n))) = n) by
           (rewrite Nat2Z.id; apply valZpK).
         rewrite -eqnp.
         apply (bound_is_a_unit (Z.of_nat (nat_of_ord n))).
         - apply Hnnonzero.
         - apply inj_lt.
           pose proof (ltn_ord n) as Hnlep.
           apply (reflect_iff _ _ (@ssrnat.ltP _ _)) in Hnlep.
           rewrite /Zp_trunc in Hnlep. simpl in Hnlep.
           apply Hnlep.
  Defined.
  
  Definition Zp_nonzero_to_unit (n : 'Z_p) (Hnnonzero : (1 ≤ n)%Z) : Zpx :=
    FinRing.Unit (bound_is_a_unit_Zp n Hnnonzero).
  
  Definition Zp_to_unit (n : 'Z_p) : option Zpx :=
    let b := ((nat_of_ord n) <? p)%nat in
    if b then
      match Z_le_dec 1 (Z.of_nat (nat_of_ord n)) with
      | left Hnnonzero => Some (Zp_nonzero_to_unit n Hnnonzero)
      | right _ => None
      end
    else None.

  Definition unit_to_Zp (g : Zpx) : 'Z_p := FinRing.uval g.

  Definition int_of_vg_sem_p (n : Zpx) : nat := nat_of_ord (unit_to_Zp n).
  
  Definition vg_of_int_sem_p (n : nat) : option Zpx := 
    let bbound := bool_decide ((@inZp (S p'') n) < p)%nat in
    let bnonzero := bool_decide (1 ≤ @inZp (S p'') (Z.to_nat n))%nat in
    if (1 <=? n)%nat && (n <? p)%nat then
      Zp_to_unit (@inZp (S p'') n)
    else None.


  Lemma int_of_vg_sem_p_bound : 
    ∀ g : vgG, (int_of_vg_sem_p g < S (#|pred_of_set [set: fingroup_FinGroup__to__fintype_Finite vgG]|))%nat. 
  Proof. 
    intros g.
    unshelve erewrite vgG_card; first exact vgg_p.
    assert (S (S n'') = S (S p'')) as ->. 
    { admit. }
    apply Nat.lt_succ_r. 
    eapply (leq_zmodp (p'')).
  Admitted. 

  Lemma vg_of_int_of_vg_sem_p (n : nat) (x : vgG) :
    vg_of_int_sem_p n = Some x → int_of_vg_sem_p x = n.
  Proof.
    intros Hsome. unfold vg_of_int_sem_p, int_of_vg_sem_p in *.
    destruct (1 <=? n) eqn:Hnz; last (rewrite andb_false_l in Hsome; inversion Hsome).
    destruct (n <? p) eqn:Hbound; last (rewrite andb_false_r in Hsome; inversion Hsome).
    rewrite andb_diag /Zp_to_unit in Hsome.
    destruct (nat_of_ord (inZp n) <? p) eqn:Hin; last inversion Hsome.
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord (inZp n)))) eqn:Hnonzero; inversion Hsome.
    subst. 
  Admitted. 

  (* **************************************** *)

  Import valgroup_tactics.
  Context `{!probblazeRGS Σ}.

  (* Fact int_of_vg_lrel_G_p :
       ⊢ (lrel_G (vg:=vg_p) → lrel_int)%lrel int_of_vg int_of_vg.
     Proof with rel_pures.
       iIntros "!>" (??) "(%v&->&->)".
       unfold int_of_vg, cgs_p, int_of_vg_p... rel_vals.
     Qed. *)

  Definition vg_of_int_unpacked (x : Z) (vmin : (1 ≤ x)%Z) (vmax : (x < p)%Z) : Zpx.
  Proof.
    unshelve econstructor.
    - exists (Z.to_nat x). rewrite Zp_cast //. apply /ssrnat.leP. lia.
    - rewrite qualifE /=. rewrite Zp_cast //.
      destruct x as [|xpos | xneg] eqn:hx ; [|shelve|].
      { exfalso. destruct vmin. simpl. by reflexivity. }
      exfalso ; by destruct vmin.
      Unshelve.
      rewrite prime.prime_coprime //.
      rewrite -hx. rewrite -hx in vmin, vmax.
      apply /negP => h.
      unshelve epose proof (div.dvdn_leq _ h) as lepx => // ; [apply /ssrnat.leP ; lia|].
      move /ssrnat.leP : lepx. lia.
  Defined.

  (* Fact vg_of_int_lrel_G_p :
       ⊢ (lrel_int → () + lrel_G (vg:=vg_p))%lrel vg_of_int vg_of_int.
     Proof with rel_pures.
       iIntros "!>" (??) "(%v&->&->)". unfold vg_of_int, cgs_p, vg_of_int_p...
       case_bool_decide as vmin ; rel_pures ; [case_bool_decide as vmax|]...
       all: rel_vals.
       iExists (vg_of_int_unpacked v vmin vmax) => /=.
       rewrite /vgval_p /=. rewrite Z2Nat.id //. lia.
     Qed. *)

  Fact is_mult_p (x y : vgG) : ⊢ WP vmult x y {{ λ (v : cval), ⌜v = vgval_p (x * y)%g⌝ }}.
  Proof.
    rewrite /vmult /= /vmult_p /vgval_p /=. wp_pures.
    iPureIntro.
    rewrite -Nat2Z.inj_mul rem_modn //=. 
  Qed.

  Fact is_spec_mult_p (x y : vgG) K :
    ⤇ fill K (vmult x y) -∗ spec_update ⊤ (⤇ fill K (vgval_p (x * y)%g)).
  Proof.
    iIntros. rewrite /vmult /cgs_p /vmult_p /= /vgval_p //=. tp_pures => /=.
    by rewrite -ssrnat.multE -Nat2Z.inj_mul -rem_modn. 
  Qed. 

  Fact is_exp' (b : vgG) (x : nat) :
    {{{ True }}} vexp' vunit_p vmult_p b #x {{{ v, RET (v : cval); ⌜v = vgval_p (b ^+ x)%g⌝ }}}.
  Proof.
    unfold vexp, vexp'. iIntros (? _) "hlog".
    wp_pure. wp_pure.
    iInduction x as [|x] "IH" forall (Φ).
    - wp_pures.
      unfold vunit_p.
      iApply ("hlog").
      by rewrite expg0.
    - do 4 wp_pure.
      iApply (primitive_laws.wp_bind _ _ ((rec: _ _ := _)%V _)).
      replace (S x - 1)%Z with (Z.of_nat x) by lia.
      iApply "IH".
      iIntros. wp_pures.
      iApply (wp_frame_wand with "hlog"). rewrite H. 
      iApply (wp_mono $! (is_mult_p b (b ^+ x))).
      iIntros (??) "hlog" ; subst. iApply "hlog".
      by rewrite expgS.
  Qed.

  Fact is_spec_exp' (b : vgG) (x : nat) K :
    ⤇ fill K (vexp' vunit_p vmult_p b #x) ⊢ spec_update ⊤ (⤇ fill K (vgval_p (b ^+ x)%g)).
  Proof.
    unfold vexp, vexp'. iIntros "hlog".
    tp_pure. tp_pure.
    iInduction x as [|x] "IH" forall (K).
    - tp_pures. iModIntro.
      iApply ("hlog").
    - do 4 tp_pure.
      tp_bind ((rec: _ _ := _)%V _).
      replace (S x - 1)%Z with (Z.of_nat x) by lia.
      iSpecialize ("IH" with "hlog").
      iMod "IH" as "IH /=".
      rewrite fill_app //=.
      tp_pures.
      rewrite expgS.
      by iApply is_spec_mult_p.
  Qed.

  Fact Zpx_small : ∀ (x : vgG), div.modn (FinRing.uval x) p = FinRing.uval x.
  Proof. move => [/= x i]. rewrite div.modn_small //. Qed.

  Fact order_inv (x : vgG) : x ^+ p'' = x^-1.
  Proof.
    eapply (mulIg x) ; rewrite mulVg ; rewrite -expgSr.
    assert (S p'' = prime.totient p) as -> by rewrite prime.totient_prime => //.
    rewrite -card_units_Zp => //=.
    simpl in x. apply expg_cardG. apply in_setT.
  Qed.

  Fact is_inv_p (x : vgG) : ⊢ WP x^-1 {{ λ (v : cval), ⌜v = (vgval_p (x^-1)%g)⌝ }}.
  Proof.
    simpl. rewrite /vinv_p {1}/vgval_p. wp_pures => /=.
    iApply (primitive_laws.wp_bind [BinOpLCtx _ _]).
    iApply is_exp' => //.
    iIntros (? ->) "!>". wp_pures. iPureIntro.
    rewrite rem_modn // /vgval_p. rewrite Zpx_small. rewrite order_inv. done.
  Qed.

  Fact is_spec_inv_p (x : vgG) K :
    ⤇ fill K x^-1 -∗ spec_update ⊤ (⤇ fill K (vgval_p (x^-1)%g)).
  Proof.
    iIntros "hlog" => /=. rewrite /vinv_p {2}/vgval_p. tp_pures => /=.
    tp_bind (vexp' _ _ _ _)%E.
    iMod (is_spec_exp' with "hlog") as "hlog /=". 
    rewrite fill_app.
    tp_pures.
    rewrite rem_modn //. rewrite Zpx_small order_inv /=.
    iModIntro. iAssumption.
  Qed.

  Lemma bool_decide_vgval_p x y : bool_decide (vgval_p x = vgval_p y) = bool_decide (x = y).
  Proof. 
    apply bool_decide_ext.
    split; [apply (inj vgval_p)|by intros ->].
  Qed. 
  
  Fact is_eq_p (x y : vgG) : ⊢ WP veq_p x y {{ λ v, ⌜ v = #(bool_decide (x = y)) ⌝ }}.
  Proof. 
    rewrite /veq_p //=.
    wp_pures.
    iPureIntro.
    by rewrite bool_decide_vgval_p.
  Qed. 

  Fact is_spec_eq_p (x y : vgG) K : ⤇ fill K (veq_p x y) -∗ spec_update ⊤ (⤇ fill K #(bool_decide (x = y))).
  Proof. 
    iIntros "Hj".
    rewrite /veq_p. 
    tp_pures.
    iModIntro.
    by rewrite bool_decide_vgval_p.
  Qed.     

  Fact τG_subtype_p v1 v2 η μ δ ξ : 𝔾 v1 v2 ⊢ interp.interp._ty η μ δ τG ξ v1 v2.
  Proof. iIntros ((w&->&->)). iExists _. eauto. Qed.

  Lemma vgval_p_typed : ∀ x : vgG, ⊢ᵥ vgval x : τG. 
  Proof. intros ?. constructor. Qed.

  Definition cg_p : clutch_group (cg := cgs_p).
    unshelve eapply (
        {| (* τG_lrel := τG_subtype_p 
           ; *) vgval_typed := vgval_p_typed
        ; is_unit := is_unit_p
        ; is_inv := is_inv_p
        ; is_mult := is_mult_p
        ; is_spec_mult := is_spec_mult_p
        ; is_spec_inv := is_spec_inv_p
        ; is_eq := is_eq_p
        ; is_spec_eq := is_spec_eq_p
        |}).
  (*   done.                       (* handles is_unit *)
     Defined. *)
  Admitted. 

 

  (* clutch_group_generator states that the val_group_generator is well-typed *)
  (* Definition cgg_p : @clutch_group_generator vg_p cgs_p vgg_p.
     Proof.
       constructor. constructor.
     Defined. *)

End Zpx.
