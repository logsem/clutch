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
  (* Group elements are represented by their unit value in [1, p-1], but the
     exposed index [int_of_vg] is 0-based, ranging over [0, p-2] = [0, #|G|-1].
     The +-1 conversion therefore lives in [int_of_vg_p] / [vg_of_int_p]. *)
  Definition int_of_vg_p := (λ:"a", "a" - #1)%V.
  Lemma int_of_vg_p_typed : ⊢ᵥ int_of_vg_p : (ℤ ⇾ ℤ).
  Proof.
    apply Rec_val_typed; first done.
    eapply BinOp_typed; [constructor | apply Var_typed |].
    apply Weakening_typed. apply Val_typed. constructor.
  Qed.
  Definition vg_of_int_p :=
    (λ:"a", if: (#0 ≤ "a") && ("a" < #(S p'')) then SOME ("a" + #1) else NONE)%V.
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
    - apply InjR_typed.
      eapply BinOp_typed; [constructor | apply Var_typed |].
      apply Val_typed. constructor.
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
  (* Semantic conversion functions *)
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

  Lemma uval_nonzero (g : Zpx) : (1 ≤ unit_to_Zp g)%Z.
  Proof.
    destruct g as [x H].
    generalize dependent H.
    rewrite /in_mem.
    rewrite /ssralg.GRing.unit.
    rewrite /mem. simpl.
    rewrite /Zp_trunc. simpl.
    rewrite /div.coprime.
    destruct (zerop x) as [eq|ineq].
    - rewrite eq. rewrite /div.gcdn.
      rewrite /div.egcdn_rec. simpl.
      intro contra.
      discriminate contra.
    - intro H; clear H.
      replace 1%Z with (Z.of_nat 1) by lia.
      apply inj_le. assumption.
  Defined.
  Lemma unit_to_Zp_nonzero (g : Zpx) : (1 ≤ unit_to_Zp g)%Z.
  Proof.
    rewrite /unit_to_Zp.
    apply uval_nonzero.
  Qed.

  Definition int_of_vg_sem_p (n : Zpx) : nat :=
    Nat.pred (nat_of_ord (unit_to_Zp n)).

  Definition vg_of_int_sem_p (n : nat) : option Zpx :=
    if (n <? S p'')%nat then Zp_to_unit (@inZp (S p'') (S n)) else None.


  Lemma int_of_vg_sem_p_bound :
    ∀ g : vgG, (int_of_vg_sem_p g < #|pred_of_set [set: fingroup_FinGroup__to__fintype_Finite vgG]|)%nat.
  Proof.
    intros g.
    assert (Hlt : (nat_of_ord (unit_to_Zp g) < p)%nat).
    { rewrite /unit_to_Zp. pose proof (ltn_ord (FinRing.uval g)) as H'.
      move/ssrnat.leP in H'. exact H'. }
    assert (Hpred : forall k : nat, Nat.pred k = (k - 1)%nat)
      by (intro k; destruct k; simpl; lia).
    unfold int_of_vg_sem_p.
    rewrite card_units_Zp; last done.
    rewrite (prime.totient_prime p_prime).
    rewrite !Hpred.
    lia.
  Qed.


  (* Stated with [m] abstract so the guards can be destructed: the branches of
     [Zp_to_unit] depend on the scrutinee, which blocks [destruct] once [m] is
     an applied term. *)
  Lemma Zp_to_unit_uval (m : 'Z_p) (x : Zpx) :
    Zp_to_unit m = Some x → unit_to_Zp x = m.
  Proof.
    rewrite /Zp_to_unit /unit_to_Zp.
    destruct (nat_of_ord m <? p)%nat; last discriminate.
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord m))) as [Hle|Hgt]; last discriminate.
    intro Heq. inversion Heq. reflexivity.
  Qed.

  Lemma Zp_to_unit_isSome (m : 'Z_p) :
    (1 <= nat_of_ord m)%nat → (nat_of_ord m < p)%nat →
    exists x : Zpx, Zp_to_unit m = Some x.
  Proof.
    intros H1 H2. rewrite /Zp_to_unit.
    rewrite (proj2 (Nat.ltb_lt _ _) H2).
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord m))) as [Hle|Hgt]; last lia.
    eexists. reflexivity.
  Qed.

  Lemma vg_of_int_of_vg_sem_p (n : nat) (x : vgG) :
    vg_of_int_sem_p n = Some x → int_of_vg_sem_p x = n.
  Proof.
    intros Hsome. unfold vg_of_int_sem_p, int_of_vg_sem_p in *.
    destruct (n <? S p'')%nat eqn:Hbound; last inversion Hsome.
    rewrite Nat.ltb_lt in Hbound.
    apply Zp_to_unit_uval in Hsome. rewrite Hsome.
    assert (Hmod : nat_of_ord (@inZp (S p'') (S n)) = S n).
    { simpl. apply div.modn_small. rewrite Rcomplements.SSR_leq. lia. }
    rewrite Hmod. reflexivity.
  Qed.

  (* [Hlt] and [Hnz] are stated over [unit_to_Zp xg] rather than over
     [FinRing.uval xg]: the two are convertible, but [lia] needs the atom to
     match the goal *syntactically* (the goal's copy carries [Zp_trunc p] in
     its coercion where [ltn_ord]'s carries [p''] already reduced). *)
  Fact int_of_vg_of_int_sem_p : ∀ (xg : vgG),
      vg_of_int_sem_p (int_of_vg_sem_p xg) = Some xg.
  Proof.
    intros xg.
    assert (Hlt : (nat_of_ord (unit_to_Zp xg) < p)%nat).
    { rewrite /unit_to_Zp. pose proof (ltn_ord (FinRing.uval xg)) as H'.
      move/ssrnat.leP in H'. exact H'. }
    pose proof (valP xg) as Hu.
    assert (Hnz : nat_of_ord (unit_to_Zp xg) = 0%nat -> False).
    { rewrite /unit_to_Zp. intro h0.
      assert (Hc : is_true (div.coprime p (nat_of_ord (FinRing.uval xg)))).
      { rewrite -unitZpE; last done. rewrite natr_Zp. exact Hu. }
      rewrite h0 /div.coprime div.gcdn0 in Hc. move/eqP in Hc. discriminate. }
    assert (Hpred : forall k : nat, Nat.pred k = (k - 1)%nat).
    { intro k; destruct k; simpl; lia. }
    unfold vg_of_int_sem_p, int_of_vg_sem_p.
    rewrite !Hpred.
    assert (Hb : ((nat_of_ord (unit_to_Zp xg) - 1) <? S p'')%nat = true).
    { apply Nat.ltb_lt. lia. }
    rewrite Hb.
    assert (Hs : S (nat_of_ord (unit_to_Zp xg) - 1) = nat_of_ord (unit_to_Zp xg))
      by lia.
    rewrite Hs.
    assert (Hge1 : (1 <= nat_of_ord (unit_to_Zp xg))%nat).
    { destruct (Nat.eq_dec (nat_of_ord (unit_to_Zp xg)) 0%nat) as [E|E];
        [exfalso; exact (Hnz E) | lia]. }
    rewrite valZpK /Zp_to_unit.
    rewrite (proj2 (Nat.ltb_lt _ _) Hlt).
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord (unit_to_Zp xg))))
      as [Hle|Hgt]; last lia.
    f_equal. apply val_inj. done.
  Qed.

  (* **************************************** *)

  Import valgroup_tactics.
  Context `{!probblazeRGS Σ}.

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

  Lemma dec_left (A : Prop) (d : {A} + {~ A}) : A -> exists h, d = left h.
  Proof.
    intro a; destruct d as [h | n].
    - exists h; reflexivity.
    - exfalso; exact (n a).
  Qed.

  Lemma Zle_dec_modn (x p : nat) :
    (x < p)%nat -> (1 <=? x) = true ->
    exists H, Z_le_dec 1 (Z.of_nat (div.modn x p)) = left H.
  Proof.
    intros hxp h1.
    assert (hmod : div.modn x p = x). { apply div.modn_small. apply Rcomplements.SSR_leq. lia. }
    assert (h1' : (1 <= x)%nat) by (apply Nat.leb_le; exact h1).
    assert (key : (1 <= Z.of_nat (div.modn x p))%Z) by (rewrite hmod; lia).
    exact (dec_left _ _ key).
  Qed.

  Definition cg_p : clutch_group (cg := cgs_p).
    unshelve eapply (
        {| τG_subtype := τG_subtype_p 
        ; vgval_typed := vgval_p_typed
        ; is_unit := is_unit_p
        ; is_inv := is_inv_p
        ; is_mult := is_mult_p
        ; is_spec_mult := is_spec_mult_p
        ; is_spec_inv := is_spec_inv_p
        ; is_eq := is_eq_p
        ; is_spec_eq := is_spec_eq_p
        ; int_of_vg_sem := int_of_vg_sem_p
        ; int_of_vg_sem_bound := int_of_vg_sem_p_bound
        ; vg_of_int_sem := vg_of_int_sem_p
        ; vg_of_int_of_vg_sem := vg_of_int_of_vg_sem_p
        ; int_of_vg_of_int_sem := int_of_vg_of_int_sem_p
        |}).
    (* [int_of_vg] subtracts one: the unit value lives in [1, p-1] while the
       exposed index lives in [0, p-2]. *)
    1,2 : iIntros (E K g X R2 e) "Hbrel /="; unfold int_of_vg_p; brel_pures;
      pose proof (unit_to_Zp_nonzero g) as H1; rewrite /unit_to_Zp in H1;
      assert (Hpred : forall k : nat, Nat.pred k = (k - 1)%nat)
        by (intro k; destruct k; simpl; lia);
      replace (Z.of_nat (nat_of_ord (FinRing.uval g)) - 1)%Z
        with (Z.of_nat (int_of_vg_sem_p g))
        by (rewrite /int_of_vg_sem_p /unit_to_Zp Hpred; lia);
      iApply "Hbrel".
    (* [vg_of_int] adds one back; the guard is now [0 <= a < p-1]. *)
    1,2 : iIntros (E K X R2 e x g Heq) "Hbrel /="; unfold vg_of_int_p;
      brel_pures; unfold vg_of_int_sem_p in Heq;
      destruct (x <? S p'')%nat eqn:Hbound; last inversion Heq;
      rewrite Nat.ltb_lt in Hbound;
      apply Zp_to_unit_uval in Heq;
      rewrite bool_decide_eq_true_2; [|lia]; brel_pures;
      rewrite bool_decide_eq_true_2; [|lia]; brel_pures;
      assert (Hval : nat_of_ord (unit_to_Zp g) = S x)
        by (rewrite Heq; simpl; apply div.modn_small;
            rewrite Rcomplements.SSR_leq; lia);
      rewrite /unit_to_Zp in Hval;
      rewrite /vgval_p Hval;
      replace (Z.of_nat x + 1)%Z with (Z.of_nat (S x)) by lia;
      iApply "Hbrel".
    (* [None] can only come from the range check failing. *)
    1,2 : iIntros (E K X R2 e x Heq) "Hbrel /="; unfold vg_of_int_p;
      brel_pures; unfold vg_of_int_sem_p in Heq;
      destruct (x <? S p'')%nat eqn:Hbound;
      [ exfalso; rewrite Nat.ltb_lt in Hbound;
        assert (Hmod : nat_of_ord (@inZp (S p'') (S x)) = S x)
          by (simpl; apply div.modn_small; rewrite Rcomplements.SSR_leq; lia);
        assert (Hlo : (1 <= nat_of_ord (@inZp (S p'') (S x)))%nat) by lia;
        assert (Hhi : (nat_of_ord (@inZp (S p'') (S x)) < p)%nat) by lia;
        destruct (Zp_to_unit_isSome _ Hlo Hhi) as [y Hy];
        rewrite Hy in Heq; inversion Heq
      | rewrite Nat.ltb_ge in Hbound;
        rewrite bool_decide_eq_true_2; [|lia]; brel_pures;
        rewrite bool_decide_eq_false_2; [|lia]; brel_pures;
        iApply "Hbrel" ].
  Qed.
 
End Zpx.
