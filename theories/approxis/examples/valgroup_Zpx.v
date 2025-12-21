From clutch.approxis Require Import approxis.
From clutch.prob_lang.typing Require Import tychk.

#[warning="-hiding-delimiting-key,-overwriting-delimiting-key,-notation-incompatible-prefix"]
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool zmodp.

From clutch.prelude Require Import mc_stdlib.
From clutch.approxis.examples Require Import valgroup iterable_expression.

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

  #[local] Definition cval := prob_lang.val.
  Definition Zpx : finGroupType := FinGroup.clone _ {unit 'Z_p}.

  Definition vgval_p (n : Zpx) : cval := #(Z.of_nat (nat_of_ord (FinRing.uval n))).

  Fact vgval_inj_p : Inj eq eq vgval_p.
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
  Definition vmult_p := (λ:"a" "b", ("a" * "b") `rem` #p)%V.
  Definition vinv_p := (λ:"x", (vexp' vunit_p vmult_p "x" (#p'')) `rem` #p)%V.
  
  Definition int_of_vg_p := (λ:"a", "a")%V.
  Definition vg_of_int_p :=
    (λ:"a", if: (#1 ≤ "a") && ("a" < #p) then SOME "a" else NONE)%V.

  Instance cgs_p : clutch_group_struct.
  Proof using p'''.
    unshelve eapply ({|
          vunit := vunit_p ;
          vinv := vinv_p ;
          vmult := vmult_p ;
          int_of_vg := int_of_vg_p ;
          vg_of_int := vg_of_int_p ;
          τG := TInt ;
        |}) .
    all: cbv ; tychk.
  Defined.

  Context `{p_prime : is_true (prime.prime p)}.

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
    let b := (Z.of_nat (nat_of_ord n) <? Z.of_nat p)%Z in
    if b then
      match Z_le_dec 1 (Z.of_nat (nat_of_ord n)) with
        | left Hnnonzero => Some (Zp_nonzero_to_unit n Hnnonzero)
        | right _ => None
      end
    else None.


  Lemma Zp_to_unit_nonzero (n : 'Z_p) : (1 ≤ n)%Z → ∃ g, Zp_to_unit n = Some g.
  Proof. intros Hnonzero.
    rewrite /Zp_to_unit.
    assert (eqtmp : (Z.of_nat (nat_of_ord n) <? Z.of_nat p)%Z = true).
    { apply Z.ltb_lt. apply inj_lt.
      apply (reflect_iff _ _ (@ssrnat.ltP _ _)).
      apply ltn_ord. }
    rewrite eqtmp; clear eqtmp.
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord n))) as [Hnonzero'|contra].
    - eexists. reflexivity.
    - exfalso. apply contra. apply Hnonzero.
  Qed.

  Lemma uvalUnit : forall (n : 'Z_p)
    (H : is_true (n \is a (@ssralg.GRing.unit ('Z_p : finUnitRingType)))),
    FinRing.uval
      (FinRing.Unit
        H)
    = n.
  Proof. intros *.
    rewrite /FinRing.uval. reflexivity.
  Qed.

  (* proving either of the following suffices to carry out
    everything else *)
  Lemma Unituval : forall (g : Zpx)
    (H : is_true ((FinRing.uval g) \is a (@ssralg.GRing.unit ('Z_p : finUnitRingType)))),
    FinRing.Unit H == g.
  Proof. intros g.
    rewrite /FinRing.uval. intro H.
    rewrite /Zp_trunc. simpl.
    rewrite /reverse_coercion.
    destruct g.
    (* Locate "==". *)
  Abort.

  Lemma test0 (g : Zpx) : is_true (FinRing.uval g  \is a ssralg.GRing.unit).
  Proof. rewrite /FinRing.uval. destruct g. apply i. Qed.

  Lemma test : forall (g : Zpx),
    let '@FinRing.Unit _ x H := g in
    FinRing.Unit H = g.
  Proof. intros *. destruct g. reflexivity. Qed.
  (* Print uval_nonzero.
  Print bound_is_a_unit. *)
  Lemma Unituval_bound : forall (g : Zpx),
    FinRing.Unit (bound_is_a_unit_Zp (FinRing.uval g) (uval_nonzero g)) = g.
  Proof. intro g.
    rewrite /FinRing.uval.
    rewrite /Zp_trunc. simpl. destruct g. simpl. f_equal.
    rewrite /bound_is_a_unit_Zp.
  Abort.

  Lemma Zp_to_unit_to_Zp (n : 'Z_p) (g : Zpx) :
    Zp_to_unit n = Some g →
      unit_to_Zp g = n.
  Proof. rewrite /Zp_to_unit.
    assert (eqtmp : (Z.of_nat (nat_of_ord n) <? Z.of_nat p)%Z = true).
    { apply Z.ltb_lt. apply inj_lt.
      apply (reflect_iff _ _ (@ssrnat.ltP _ _)).
      apply ltn_ord. }
    rewrite eqtmp; clear eqtmp.
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord n))) as [Hnonzero'|contra].
    - intro H; injection H; clear H; intro H; subst.
      rewrite /unit_to_Zp. rewrite /Zp_nonzero_to_unit.
      apply uvalUnit.
    - intro H; discriminate H.
  Qed.

  Lemma unit_to_Zp_to_unit (g : Zpx) :
    Zp_to_unit (unit_to_Zp g) = Some g.
  Proof.
    rewrite /unit_to_Zp.
    rewrite /Zp_to_unit.
    assert (eqtmp : (Z.of_nat (nat_of_ord (FinRing.uval g)) <? Z.of_nat p)%Z = true).
    { apply Z.ltb_lt. apply inj_lt.
      apply (reflect_iff _ _ (@ssrnat.ltP _ _)).
      apply ltn_ord. }
    rewrite eqtmp; clear eqtmp.
    destruct (Z_le_dec 1 (Z.of_nat (nat_of_ord (FinRing.uval g)))) as [Hnonzero'|contra].
    - rewrite /Zp_nonzero_to_unit.
    Fail (rewrite Unituval; reflexivity). Abort.
    (* - exfalso. apply contra.
      apply unit_to_Zp_nonzero. Qed. *)

  Definition int_of_vg_sem_p (n : Zpx) : Z := nat_of_ord (unit_to_Zp n).
  
  Definition vg_of_int_sem_p (n : Z) : option Zpx := 
    let bbound := bool_decide (@inZp (S p'') (Z.to_nat n) < p)%Z in
    let bnonzero := bool_decide (1 ≤ @inZp (S p'') (Z.to_nat n))%Z in 
    if (1 <=? n)%Z && (n <? p)%Z then
      Zp_to_unit (@inZp (S p'') (Z.to_nat n))
    else None.

  Import valgroup_tactics.
  Context `{!approxisRGS Σ}.

  Fact int_of_vg_lrel_G_p :
    ⊢ (lrel_G (vg:=vg_p) → lrel_int)%lrel int_of_vg int_of_vg.
  Proof with rel_pures.
    iIntros "!>" (??) "(%v&->&->)".
    unfold int_of_vg, cgs_p, int_of_vg_p... rel_vals.
  Qed.

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

  Fact vg_of_int_lrel_G_p :
    ⊢ (lrel_int → () + lrel_G (vg:=vg_p))%lrel vg_of_int vg_of_int.
  Proof with rel_pures.
    iIntros "!>" (??) "(%v&->&->)". unfold vg_of_int, cgs_p, vg_of_int_p...
    case_bool_decide as vmin ; rel_pures ; [case_bool_decide as vmax|]...
    all: rel_vals.
    iExists (vg_of_int_unpacked v vmin vmax) => /=.
    rewrite /vgval_p /=. rewrite Z2Nat.id //. lia.
  Qed.

  Fact vg_of_int_correct_p `{approxisRGS Σ} :
    @det_val_fun1 _ _ Z (option vgG) lrel_int (() + lrel_G)%lrel (λ x, #x)
      (λ x, match x with
        | None => NONEV
        | Some x => SOMEV (vgval x) end) vg_of_int vg_of_int_sem_p.
  Proof with (rel_pures_l; rel_pures_r). rewrite /det_val_fun1.
    intros *. iIntros "[H G]". rewrite /to_val_type_rel. 
    assert (eqargmodp : (arg < p)%Z → div.modn (Z.to_nat arg) p = Z.to_nat arg).
    { intro Hbound. rewrite div.modn_small; first lia.
      rewrite /Zp_trunc. simpl.
      assert (Hbound' : (Z.to_nat arg < p)%nat) by lia.
      apply (reflect_iff _ _ (@ssrnat.ltP _ _)) in Hbound'.
      apply Hbound'. }
    iSplit; iIntros "Hsem".
    - rewrite /vg_of_int. simpl. rewrite /vg_of_int_p...
      rewrite /vg_of_int_sem_p.
      destruct (bool_decide (1 ≤ arg)%Z) eqn:Hargnonzero...
      + destruct (bool_decide (arg < p)%Z) eqn:Hargbound...
        * apply bool_decide_eq_true in Hargnonzero.
          apply bool_decide_eq_true in Hargbound.
          assert (Hargnonzero' : (1 ≤ (@inZp (S (S p''')) (Z.to_nat arg)))%Z).
          { rewrite /Zp_trunc. simpl.
            rewrite eqargmodp; lia. }
          pose proof (Zp_to_unit_nonzero (inZp (Z.to_nat arg)) Hargnonzero') as
           [xg eqxg]. rewrite eqxg.
          apply Z.leb_le in Hargnonzero.
          apply Z.ltb_lt in Hargbound as Hargbound'.
          rewrite Hargnonzero Hargbound'. simpl.
          rewrite /vgval_p.
          assert (eqxgtmp : FinRing.uval xg = unit_to_Zp xg).
          { rewrite /unit_to_Zp. reflexivity. }
          rewrite eqxgtmp; clear eqxgtmp.
          erewrite Zp_to_unit_to_Zp; last apply eqxg.
          rewrite /Zp_trunc. simpl.
          rewrite eqargmodp; last lia. rewrite Z2Nat.id; last lia.
          iAssumption.
        * apply bool_decide_eq_true in Hargnonzero.
          apply bool_decide_eq_false in Hargbound.
          apply Z.leb_le in Hargnonzero.
          apply Z.ltb_nlt in Hargbound.
          rewrite Hargnonzero Hargbound. simpl.
          iAssumption.
      + apply bool_decide_eq_false in Hargnonzero.
        apply Z.leb_nle in Hargnonzero.
        rewrite Hargnonzero. simpl.
        iAssumption.
    - rewrite /vg_of_int. simpl. rewrite /vg_of_int_p...
      rewrite /vg_of_int_sem_p.
      destruct (bool_decide (1 ≤ arg)%Z) eqn:Hargnonzero...
      + destruct (bool_decide (arg < p)%Z) eqn:Hargbound...
        * apply bool_decide_eq_true in Hargnonzero.
          apply bool_decide_eq_true in Hargbound.
          assert (Hargnonzero' : (1 ≤ (@inZp (S (S p''')) (Z.to_nat arg)))%Z).
          { rewrite /Zp_trunc. simpl.
            rewrite eqargmodp; lia. }
          pose proof (Zp_to_unit_nonzero (inZp (Z.to_nat arg)) Hargnonzero') as
           [xg eqxg]. rewrite eqxg.
          apply Z.leb_le in Hargnonzero.
          apply Z.ltb_lt in Hargbound as Hargbound'.
          rewrite Hargnonzero Hargbound'. simpl.
          rewrite /vgval_p.
          assert (eqxgtmp : FinRing.uval xg = unit_to_Zp xg).
          { rewrite /unit_to_Zp. reflexivity. }
          rewrite eqxgtmp; clear eqxgtmp.
          erewrite Zp_to_unit_to_Zp; last apply eqxg.
          rewrite /Zp_trunc. simpl.
          rewrite eqargmodp; last lia. rewrite Z2Nat.id; last lia.
          iAssumption.
        * apply bool_decide_eq_true in Hargnonzero.
          apply bool_decide_eq_false in Hargbound.
          apply Z.leb_le in Hargnonzero.
          apply Z.ltb_nlt in Hargbound.
          rewrite Hargnonzero Hargbound. simpl.
          iAssumption.
      + apply bool_decide_eq_false in Hargnonzero.
        apply Z.leb_nle in Hargnonzero.
        rewrite Hargnonzero. simpl.
        iAssumption.
  Qed.

  Fact int_of_vg_correct_p `{approxisRGS Σ} :
    @det_val_fun1 _ _ vgG Z lrel_G lrel_int vgval (λ x, #x) int_of_vg int_of_vg_sem_p.
  Proof with rel_pures_l; rel_pures_r.
    rewrite /det_val_fun1.
    intros *. iIntros "[H G]". rewrite /to_val_type_rel.
    iSplit; iIntros "Hsem".
    - rewrite /int_of_vg. simpl. rewrite /int_of_vg_p...
      rewrite /int_of_vg_sem_p. rewrite /vgval_p...
      rewrite /unit_to_Zp. iAssumption.
    - rewrite /int_of_vg. simpl. rewrite /int_of_vg_p...
      rewrite /int_of_vg_sem_p. rewrite /vgval_p...
      rewrite /unit_to_Zp. iAssumption.
  Qed.

  Fact int_of_vg_of_int_sem_p : ∀ (xg : vgG),
    vg_of_int_sem_p (int_of_vg_sem_p xg) = Some xg.
  Proof.
    intros xg. rewrite /int_of_vg_sem_p.
    rewrite /vg_of_int_sem_p.
    rewrite Nat2Z.id. rewrite valZpK.
    Fail rewrite unit_to_Zp_to_unit. Abort.
    (* pose proof (unit_to_Zp_nonzero xg) as H.
    apply Z.leb_le in H. rewrite H; clear H. simpl.
    pose proof (leq_ord (unit_to_Zp xg)) as Hxgbound'.
    rewrite /Zp_trunc in Hxgbound'. simpl in Hxgbound'.
    assert (Hxgbound : ((unit_to_Zp xg) < p)%Z).
    { rewrite /Zp_trunc. simpl.
      apply (reflect_iff _ _ (@leP (unit_to_Zp xg) (S p''))) in Hxgbound'.
      apply inj_lt.
      apply PeanoNat.le_lt_n_Sm. apply Hxgbound'. }
    apply Z.ltb_lt in Hxgbound. rewrite Hxgbound.
    reflexivity.
  Qed. *)

  Fact vg_of_int_of_vg_sem_p : ∀ (n : Z) (xg : vgG),
    vg_of_int_sem_p n = Some xg →
    int_of_vg_sem_p xg = n.
  Proof.
    intros n xg.
    rewrite /vg_of_int_sem_p/int_of_vg_sem_p.
    destruct (1 <=? n)%Z eqn:Hnnonzero;
    destruct (n <? p)%Z eqn:Hnbound; simpl;
    try (intro contra; discriminate contra).
    intro H.
    erewrite Zp_to_unit_to_Zp.
    - Unshelve. 2: exact (inZp (Z.to_nat n)).
      apply Z.ltb_lt in Hnbound.
      rewrite /Zp_trunc. simpl.
      rewrite div.modn_small; first apply Z2Nat.id; first lia.
      assert (Hbound' : (Z.to_nat n < p)%nat) by lia.
      apply (reflect_iff _ _ (@ssrnat.ltP _ _)) in Hbound'.
      apply Hbound'.
    - apply H.
  Qed.

  Fact vgval_sem_typed_p : ⊢ to_val_type_rel lrel_G vgval.
  Proof. iIntros (x). rewrite /vgval. simpl.
    rewrite /vgval_p. rewrite /lrel_G. 
    rewrite /lrel_car. iExists x; done.
  Qed.

  Fact is_mult_p (x y : vgG) : ⊢ WP vmult (vgval x) (vgval y) {{ λ (v : cval), ⌜v = vgval (x * y)%g⌝ }}.
  Proof.
    rewrite /vmult /= /vmult_p /vgval_p /=. wp_pures. iPureIntro.
    rewrite -Nat2Z.inj_mul. rewrite rem_modn //.
  Qed.

  Fact is_spec_mult_p (x y : vgG) K :
    ⤇ fill K (vmult (vgval x) (vgval y)) -∗ spec_update ⊤ (⤇ fill K (vgval (x * y)%g)).
  Proof.
    iIntros. rewrite /vmult /cgs_p /vmult_p /= /vgval_p. tp_pures => /=.
    iModIntro.
    by rewrite -Nat2Z.inj_mul -ssrnat.multE rem_modn.
  Qed.

  Fact is_exp' (b : vgG) (x : nat) :
    {{{ True }}} vexp' vunit_p vmult_p (vgval b) #x {{{ v, RET (v : cval); ⌜v = vgval (b ^+ x)%g⌝ }}}.
  Proof.
    unfold vexp, vexp'. iIntros (? _) "hlog".
    wp_pure. wp_pure.
    iInduction x as [|x] "IH" forall (Φ).
    - wp_pures.
      unfold vunit_p.
      iApply ("hlog").
      by rewrite expg0.
    - do 4 wp_pure.
      wp_bind ((rec: _ _ := _)%V _).
      replace (S x - 1)%Z with (Z.of_nat x) by lia.
      iApply "IH".
      iIntros. wp_pures.
      iApply (wp_frame_wand with "hlog").
      rewrite H.
      iApply (wp_mono $! (is_mult_p b (b ^+ x))).      
      iIntros (??) "hlog" ; subst. iApply "hlog".
      by rewrite expgS.
  Qed.

  Fact is_spec_exp' (b : vgG) (x : nat) K :
    ⤇ fill K (vexp' vunit_p vmult_p (vgval b) #x) ⊢ spec_update ⊤ (⤇ fill K (vgval (b ^+ x)%g)).
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
      tp_pures.
      iDestruct (is_spec_mult_p with "IH") as "IH".
      by rewrite expgS.
  Qed.

  Fact Zpx_small : ∀ (x : vgG), div.modn (FinRing.uval x) p = FinRing.uval x.
  Proof. move => [/= x i]. rewrite div.modn_small //. Qed.

  Fact order_inv (x : vgG) : x ^+ p'' = x^-1.
  Proof.
    eapply (mulIg x) ; rewrite mulVg ; rewrite -expgSr.
    assert (S p'' = prime.totient p) as -> by rewrite prime.totient_prime => //.
    rewrite -card_units_Zp => //=.
    apply expg_cardG. apply in_setT.
  Qed.


  Fact is_inv_p (x : vgG) : ⊢ WP vinv (vgval x)  {{ λ (v : cval), ⌜v = vgval (x^-1)%g⌝ }}.
  Proof.
    simpl. rewrite /vinv_p {1}/vgval_p. wp_pures => /=.
    wp_apply is_exp' => //.
    iIntros (? ->). wp_pures. iPureIntro.
    rewrite rem_modn // /vgval_p. rewrite Zpx_small. rewrite order_inv. done.
  Qed.

  Fact is_spec_inv_p (x : vgG) K :
    ⤇ fill K (vinv (vgval x)) -∗ spec_update ⊤ (⤇ fill K (vgval (x^-1)%g)).
  Proof.
    iIntros "hlog" => /=. rewrite /vinv_p {2}/vgval_p. tp_pures => /=.
    tp_bind (vexp' _ _ _ _)%E.
    iMod (is_spec_exp' with "hlog") as "hlog /=".
    tp_pures.
    rewrite rem_modn //. rewrite Zpx_small order_inv /=.
    iModIntro. iAssumption.
  Qed.

  Fact τG_subtype_p v1 v2 Δ : lrel_G v1 v2 ⊢ interp τG Δ v1 v2.
  Proof. iIntros ((w&->&->)). iExists _. eauto. Qed.

  Definition cg_p : clutch_group (cg := cgs_p).
    unshelve eapply (
        {| int_of_vg_lrel_G := int_of_vg_lrel_G_p
        ; vg_of_int_lrel_G := vg_of_int_lrel_G_p
        ; τG_subtype := τG_subtype_p
        ; is_unit := Logic.eq_refl
        ; is_inv := is_inv_p
        ; is_mult := is_mult_p
        ; is_spec_mult := is_spec_mult_p
        ; is_spec_inv := is_spec_inv_p
        ; int_of_vg_sem := int_of_vg_sem_p
        ; vg_of_int_sem := vg_of_int_sem_p
        ; vg_of_int_of_vg_sem := vg_of_int_of_vg_sem_p
        ; vg_of_int_correct := vg_of_int_correct_p
        ; int_of_vg_correct := int_of_vg_correct_p
        ; vgval_sem_typed := vgval_sem_typed_p
        |}).
  Defined.

  Definition vgg_p : val_group_generator (vg:=vg_p).
  Proof.
    move /cyclicP : (units_Zp_cyclic p_prime) => /= h.
    pose ((λ x, units_Zp p == cycle x) : pred {unit 'Z_p}) as P ; simpl in P.
    assert (zpgen : (∃ x, units_Zp p = cycle x) →
                    ∃ x, is_true (units_Zp p == cycle x)).
    { move => [/= x hx]. exists x. by apply /eqP. }
    destruct (sigW (zpgen h)) as [g hg].
    clear -hg p_prime ; simpl in *.
    unshelve econstructor.
    - exact g.
    - exact p'''.
    - unfold order. move /eqP : hg => <-.
      rewrite card_units_Zp //=.
      apply prime.totient_prime => //.
    - rewrite /generator /=. unfold units_Zp in hg.
      apply Is_true_eq_left. by rewrite hg.
  Defined.

  Definition cgg_p : @clutch_group_generator vg_p cgs_p vgg_p.
  Proof.
    constructor. constructor.
  Defined.

End Zpx.
