From clutch Require Import clutch.

#[warning="-hiding-delimiting-key,-overwriting-delimiting-key"] From mathcomp Require Import ssrnat.
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool ssrnat zmodp.

From clutch.prelude Require Import mc_stdlib.
From clutch.examples.crypto Require Import valgroup.

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
  Definition Zpx : finGroupType := [finGroupType of {unit 'Z_p}].

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
  Import valgroup_tactics.
  Context `{!clutchRGS Σ}.

  Fact int_of_vg_lrel_G_p :
    ⊢ (lrel_G (vg:=vg_p) → lrel_int)%lrel int_of_vg int_of_vg.
  Proof with rel_pures.
    iIntros "!>" (??) "(%v&->&->)".
    unfold int_of_vg, cgs_p, int_of_vg_p... rel_vals.
  Qed.

  Definition vg_of_int_unpacked (x : Z) (vmin : (1 ≤ x)%Z) (vmax : (x < p)%Z) : Zpx.
  Proof.
    unshelve econstructor.
    - exists (Z.to_nat x). rewrite Zp_cast //. apply /leP. lia.
    - rewrite qualifE /=. rewrite Zp_cast //.
      destruct x as [|xpos | xneg] eqn:hx ; [|shelve|].
      { exfalso. destruct vmin. simpl. by reflexivity. }
      exfalso ; by destruct vmin.
      Unshelve.
      rewrite prime.prime_coprime //.
      rewrite -hx. rewrite -hx in vmin, vmax.
      apply /negP => h.
      unshelve epose proof (div.dvdn_leq _ h) as lepx => // ; [apply /leP ; lia|].
      move /leP : lepx. lia.
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

  Fact is_mult_p (x y : vgG) : ⊢ WP vmult x y {{ λ (v : cval), ⌜v = (x * y)%g⌝ }}.
  Proof.
    rewrite /vmult /= /vmult_p /vgval_p /=. wp_pures. iPureIntro.
    rewrite -Nat2Z.inj_mul. rewrite rem_modn //.
  Qed.

  Fact is_spec_mult_p (x y : vgG) K :
    refines_right K (vmult x y) ⊢ |={⊤}=> refines_right K (x * y)%g.
  Proof.
    iIntros. rewrite /vmult /cgs_p /vmult_p /= /vgval_p. tp_pures => /=.
    by rewrite -Nat2Z.inj_mul -ssrnat.multE rem_modn.
  Qed.

  Fact is_exp' (b : vgG) (x : nat) :
    {{{ True }}} vexp' vunit_p vmult_p b #x {{{ v, RET (v : cval); ⌜v = (b ^+ x)%g⌝ }}}.
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
      iApply (wp_frame_wand with "hlog"). iApply (wp_mono $! (is_mult_p b v)).
      iIntros (??) "hlog" ; subst. iApply "hlog".
      by rewrite expgS.
  Qed.

  Fact is_spec_exp' (b : vgG) (x : nat) K :
    refines_right K (vexp' vunit_p vmult_p b #x) ⊢ |={⊤}=> refines_right K (b ^+ x)%g.
  Proof.
    unfold vexp, vexp'. iIntros "hlog".
    tp_pure. tp_pure.
    iInduction x as [|x] "IH" forall (K).
    - tp_pures.
      iApply ("hlog").
    - do 4 tp_pure.
      tp_bind ((rec: _ _ := _)%V _).
      replace (S x - 1)%Z with (Z.of_nat x) by lia.
      rewrite refines_right_bind.
      iSpecialize ("IH" with "hlog").
      iMod "IH" as "IH".
      rewrite -refines_right_bind => /=.
      tp_pures.
      rewrite is_spec_mult_p.
      by rewrite expgS.
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

  Fact is_inv_p (x : vgG) : ⊢ WP x^-1 {{ λ (v : cval), ⌜v = (x^-1)%g⌝ }}.
  Proof.
    simpl. rewrite /vinv_p {1}/vgval_p. wp_pures => /=.
    wp_apply is_exp' => //.
    iIntros (? ->). wp_pures. iPureIntro.
    rewrite rem_modn // /vgval_p. rewrite Zpx_small. rewrite order_inv. done.
  Qed.

  Fact is_spec_inv_p (x : vgG) K : refines_right K x^-1 ⊢ |={⊤}=> refines_right K (x^-1)%g.
  Proof.
    iIntros "hlog" => /=. rewrite /vinv_p {2}/vgval_p. tp_pures => /=.
    tp_bind (vexp' _ _ _ _)%E.
    rewrite refines_right_bind. iMod (is_spec_exp' with "hlog") as "hlog".
    rewrite -refines_right_bind /=. tp_pures.
    rewrite rem_modn //. rewrite Zpx_small order_inv /=. iAssumption.
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
        |}).
  Defined.

  (* TODO remove once https://github.com/math-comp/math-comp/pull/1041/files is
     merged and we use mathcomp from the future. *)
  Lemma units_Zp_cyclic : is_true (cyclic (units_Zp p)).
  Proof.
    suff: is_true (cyclic [set: {unit 'F_p}]) by rewrite prime.pdiv_id.
    exact: field_unit_group_cyclic.
  Qed.

  Definition cgg_p : clutch_group_generator (vg:=vg_p).
  Proof.
    move /cyclicP : units_Zp_cyclic => /= h.
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

End Zpx.
