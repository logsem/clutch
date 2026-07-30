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
  Lemma vunit_p_typed : ⊢ᵥ vunit_p : ℤ. 
  Proof. apply Int_val_typed. Qed.
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
  (* Proof.
       simpl. rewrite /vinv_p {1}/vgval_p. wp_pures => /=.
       wp_apply is_exp' => //.
       iIntros (? ->). wp_pures. iPureIntro.
       rewrite rem_modn // /vgval_p. rewrite Zpx_small. rewrite order_inv. done.
     Qed. *)
  Admitted. 

  Fact is_spec_inv_p (x : vgG) K :
    ⤇ fill K x^-1 -∗ spec_update ⊤ (⤇ fill K (vgval_p (x^-1)%g)).
  Proof.
  (*   iIntros "hlog" => /=. rewrite /vinv_p {2}/vgval_p. tp_pures => /=.
       tp_bind (vexp' _ _ _ _)%E.
       iMod (is_spec_exp' with "hlog") as "hlog /=".
       tp_pures.
       rewrite rem_modn //. rewrite Zpx_small order_inv /=.
       iModIntro. iAssumption.
     Qed. *)
  Admitted.

  Fact is_eq_p (x y : vgG) : ⊢ WP veq_p x y {{ λ v, ⌜ v = #(bool_decide (x = y)) ⌝ }}.
  Admitted.

  Fact is_spec_eq_p (x y : vgG) K : ⤇ fill K (veq_p x y) -∗ spec_update ⊤ (⤇ fill K #(bool_decide (x = y))).
  Admitted.                                       
  (* Fact τG_subtype_p v1 v2 Δ : lrel_G v1 v2 ⊢ interp τG Δ v1 v2.
     Proof. iIntros ((w&->&->)). iExists _. eauto. Qed. *)

  Definition cg_p : clutch_group (cg := cgs_p).
    unshelve eapply (
        {|is_inv := is_inv_p
        ; is_mult := is_mult_p
        ; is_spec_mult := is_spec_mult_p
        ; is_spec_inv := is_spec_inv_p
        ; is_eq := is_eq_p
        ; is_spec_eq := is_spec_eq_p
        |}).
  (*   done.                       (* handles is_unit *)
     Defined. *)
  Admitted. 

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

  (* clutch_group_generator states that the val_group_generator is well-typed *)
  (* Definition cgg_p : @clutch_group_generator vg_p cgs_p vgg_p.
     Proof.
       constructor. constructor.
     Defined. *)

End Zpx.
