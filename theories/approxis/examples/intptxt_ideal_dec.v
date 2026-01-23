From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.approxis Require Import map reltac2 approxis option linked_list.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init
  advantage_laws iterable_expression.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

(*
  We show that for a nysymmetric scheme satisfying INT-PTXT,
  we can replace decryption by an idealized encryption, testing
  if the plaintext was a encrypted by the encryption oracle
  beforehand.
*)

Section logrel.
  
  Context `{!approxisRGS Σ}.

  Variable lrel_msg : lrel Σ.
  Variable lrel_cipher : lrel Σ.
  Variable lrel_key : lrel Σ.

  Variable is_ciphertext : val.
  Variable is_plaintext : val.

  Definition left_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v v'.
  Definition right_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v' v.
  Definition half_lrel (τ : lrel Σ) (v : val) : iProp Σ := left_lrel τ v ∨ right_lrel τ v.

  Definition refines_is_ciphertext_l_prop :=
    ∀ (c : val) K e E A,
        left_lrel lrel_cipher c
      -∗ refines E (fill K (Val #true)) e A
      -∗ REL (fill K (is_ciphertext c)) << e @ E : A.

  Definition refines_is_ciphertext_r_prop :=
    ∀ (c : val) K e E A,
        right_lrel lrel_cipher c
      -∗ refines E e (fill K (Val #true)) A
      -∗ REL e << (fill K (is_ciphertext c)) @ E : A.

  Definition refines_is_plaintext_l_prop :=
    ∀ (c : val) K e E A,
        left_lrel lrel_msg c
      -∗ refines E (fill K (Val #true)) e A
      -∗ REL (fill K (is_plaintext c)) << e @ E : A.

  Definition refines_is_plaintext_r_prop :=
    ∀ (c : val) K e E A,
        right_lrel lrel_msg c
      -∗ refines E e (fill K (Val #true)) A
      -∗ REL e << (fill K (is_plaintext c)) @ E : A.

  Hypothesis refines_is_ciphertext_r : refines_is_ciphertext_r_prop. 
  Hypothesis refines_is_ciphertext_l : refines_is_ciphertext_l_prop.
  Hypothesis refines_is_plaintext_r : refines_is_plaintext_r_prop. 
  Hypothesis refines_is_plaintext_l : refines_is_plaintext_l_prop. 

  Definition refines_is_key_l_prop (is_key : val) :=
    ∀ (k : val) K e E A,
        left_lrel lrel_key k
      -∗ refines E (fill K (Val #true)) e A
      -∗ REL (fill K (is_key k)) << e @ E : A.

  Definition refines_is_key_r_prop (is_key : val) :=
    ∀ (k : val) K e E A,
        right_lrel lrel_key k
      -∗ refines E e (fill K (Val #true)) A
      -∗ REL e << (fill K (is_key k)) @ E : A.
      
  Variable elem_eq : val.

  Lemma half_lrel_pers : ∀ (A : lrel Σ) x, Persistent (half_lrel A x).
  Proof. intros A x. rewrite /Persistent.
    iIntros "[[%y #H] | [%y #H]]".
    - iModIntro. iLeft. iExists y. iAssumption.
    - iModIntro. iRight. iExists y. iAssumption.
  Qed.

  Hypothesis lrel_msg_comparable : ∀ x y, (λ x, half_lrel lrel_msg x) x
    -∗ (λ x, half_lrel lrel_msg x) y
    -∗ ⌜vals_comparable x y⌝.
  Hypothesis lrel_msg_eq : ∀ x y, lrel_msg x y ⊢ ⌜x = y⌝.

  Hypothesis refines_elem_eq_l : refines_elem_eq_l_prop elem_eq
    (λ x, half_lrel lrel_msg x).
  Hypothesis refines_elem_eq_r : refines_elem_eq_r_prop elem_eq
    (λ x, half_lrel lrel_msg x).

  #[local] Instance val_inj : Inject val val.
  Proof. unshelve econstructor.
    - exact (λ x, x).
    - intros x y H'; assumption.
  Defined.

  Definition refines_elem_of_l :=
    @refines_elem_of_l elem_eq _ _ (λ x, half_lrel lrel_msg x)
      (half_lrel_pers lrel_msg) lrel_msg_comparable refines_elem_eq_l val val_inj.
  Definition refines_elem_of_r :=
    @refines_elem_of_r elem_eq _ _ (λ x, half_lrel lrel_msg x)
      (half_lrel_pers lrel_msg) lrel_msg_comparable refines_elem_eq_r val val_inj.

  Definition PTXT' : val :=
    λ: "b" "adv" "scheme" "Q_enc" "Q_dec",
      let: "record_plaintext" := init_linked_list #() in
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "enc" := get_enc "enc_scheme" in
      let: "dec" := get_dec "enc_scheme" in
      let: "key" := get_keygen "scheme" #() in
      let: "enc_key" := λ: "msg", add_list "record_plaintext" "msg";;
        "enc" "key" "msg" in
      let: "oracle_enc" := q_calls_general_test is_plaintext "Q_enc" "enc_key" in
      let: "oracle_lr" :=
        let: "counter" := ref #0 in
        λ: "c",
          if: "b" then
            if: is_ciphertext "c" then
              let: "decrypted" := "dec" "key" "c" in
              if: ! "counter" < "Q_dec" then
                "counter" <- ! "counter" + #1;;
                let: "decrypted'" := "dec" "key" "c" in
                if: elem_of_linked_list elem_eq
                  "record_plaintext" "decrypted'" then
                  SOME "decrypted"
                else
                  NONEV
              else NONEV
            else NONEV
          else
            if: is_ciphertext "c" then
              let: "decrypted" := "dec" "key" "c" in
              if: ! "counter" < "Q_dec" then
                "counter" <- ! "counter" + #1;;
                SOME "decrypted"
              else NONEV
            else NONEV
      in
      let: "b'" := "adv" "oracle_enc" "oracle_lr" in
      "b'".

  Definition adv_PTXT' : val :=
    λ: "adv" "enc_oracle" "dec_oracle" "ver_oracle",
      let: "rr_key_b" :=
        λ: "c",
          let: "decrypted" := "dec_oracle" "c" in
          match: "ver_oracle" "c" with
            | NONE => NONE
            | SOME "b" => if: "b" then
                "decrypted"
              else
                NONE
          end in
      let: "oracle_lr" := "rr_key_b" in
      "adv" "enc_oracle" "oracle_lr".

  Context `{SYM_init}.

  Variable senc : list loc → val.
  Variable sdec : list loc → val.

  Variable P0l : list loc → iProp Σ.
  Variable P0r : list loc → iProp Σ.

  Variable Pl : list loc → iProp Σ.
  Variable Pr : list loc → iProp Σ.
  Variable Plr : list loc → list loc → iProp Σ.

  Definition P0_P_l_prop := ∀ lls, P0l lls -∗ Pl lls.
  Definition P0_P_r_prop := ∀ rls, P0r rls -∗ Pr rls.
  Definition P0lr_Plr_prop := ∀ lls rls, P0l lls -∗ P0r rls -∗ Plr lls rls.
  Hypothesis P0_P_l : P0_P_l_prop.
  Hypothesis P0_P_r : P0_P_r_prop.
  Hypothesis P0lr_Plr : P0lr_Plr_prop.

  Definition refines_init_scheme_l_prop := forall K e E A,
    (∀ lls,
      P0l lls -∗
      refines E
        (fill K (senc lls, sdec lls))
        e A)
    ⊢ refines E
        (fill K (get_enc_scheme sym_scheme #()))
        e A.

  Definition refines_init_scheme_r_prop := forall K e E A,
    (∀ rls,
      P0r rls -∗
      refines E
        e
        (fill K (senc rls, sdec rls))
        A)
    ⊢ refines E
        e
        (fill K (get_enc_scheme sym_scheme #()))
        A.

  Hypothesis refines_init_scheme_l : refines_init_scheme_l_prop.

  Hypothesis refines_init_scheme_r : refines_init_scheme_r_prop.

  Definition refines_sym_keygen_couple_prop := forall K K' E A,
    (∀ key,
      (lrel_car lrel_key) key key -∗
        refines E
          (fill K  (Val key))
          (fill K' (Val key))
          A)
    ⊢ refines E
        (fill K  (keygen #()))
        (fill K' (keygen #()))
        A.
  Hypothesis refines_sym_keygen_couple : refines_sym_keygen_couple_prop.

  Let lrel_enc_oracle : lrel Σ := lrel_enc_oracle lrel_msg lrel_cipher.
  Let lrel_dec_oracle : lrel Σ := lrel_dec_oracle lrel_msg lrel_cipher.

  Definition senc_sem_typed_prop :=
    ∀ lls rls (𝒩 : namespace) (P : iProp Σ),
    (∃ (Q : iProp Σ),
      P ⊣⊢
        (Q
      ∗ Plr lls rls)
    ) →
    na_invP 𝒩 P
      ⊢ refines top (senc lls)
      (senc rls) (lrel_key → lrel_msg → lrel_cipher).

  Hypothesis senc_sem_typed : senc_sem_typed_prop.

  Definition sdec_sem_typed_prop :=
    ∀ lls rls (𝒩 : namespace) (P : iProp Σ),
    (∃ (Q : iProp Σ),
      P ⊣⊢
        (Q
      ∗ Plr lls rls)
    ) →
    na_invP 𝒩 P
      ⊢ refines top (sdec lls)
      (sdec rls) (lrel_key → lrel_cipher → lrel_msg).

  Hypothesis sdec_sem_typed : sdec_sem_typed_prop.

  Lemma forall_lrel_pers : ∀ l l' (A : lrel Σ),
    Persistent (@ForallSep2 Σ val val A l l').
  Proof. intros l l' A.
    apply ForallSep2_pers_is_pers.
    apply lrel_persistent.
  Qed.

  Lemma in_forall2_in_l : ∀ l l' f x,
    x ∈ l → (@ForallSep2 Σ val val f l l') ⊢ ∃ y, f x y ∗ ⌜y ∈ l'⌝.
  Proof. intros l l' f x Hin. iRevert (l').
    iInduction l as [|h t] "IHt"; iIntros (l') "Hforall".
    - destruct l' as [|h' t'].
      + exfalso. apply not_elem_of_nil in Hin.
        assumption.
      + iExFalso; iAssumption.
    - destruct l' as [|h' t'].
      + iExFalso; iAssumption.
      + simpl. iDestruct "Hforall" as "[Hhead Hforall]".
        inversion Hin; subst.
        * iExists h'. iFrame. iPureIntro.
          constructor.
        * iAssert (⌜x ∈ t⌝)%I as "H".
          { iPureIntro; assumption. }
          iPoseProof ("IHt" with "H Hforall") as "H'".
          clear Hin.
          iDestruct "H'" as (y) "[Hf %Hin]".
          iExists y. iFrame.
          iPureIntro; constructor.
          assumption.
  Qed.

  Lemma in_forall2_in_r : ∀ l l' f y,
    y ∈ l' → (@ForallSep2 Σ val val f l l') ⊢ ∃ x, f x y ∗ ⌜x ∈ l⌝.
  Proof. intros l l' f x Hin. iRevert (l).
    iInduction l' as [|h' t'] "IHt"; iIntros (l) "Hforall".
    - destruct l as [|h t].
      + exfalso. apply not_elem_of_nil in Hin.
        assumption.
      + iExFalso; iAssumption.
    - destruct l as [|h t].
      + iExFalso; iAssumption.
      + simpl. iDestruct "Hforall" as "[Hhead Hforall]".
        inversion Hin; subst.
        * iExists h. iFrame. iPureIntro.
          constructor.
        * iAssert (⌜x ∈ t'⌝)%I as "H".
          { iPureIntro; assumption. }
          iPoseProof ("IHt" with "H Hforall") as "H'".
          clear Hin.
          iDestruct "H'" as (y) "[Hf %Hin]".
          iExists y. iFrame.
          iPureIntro; constructor.
          assumption.
  Qed.

  Lemma dec_ideal__dec_true (adv : val) :
      ((lrel_car (lrel_enc_oracle → lrel_dec_oracle → lrel_bool)) adv adv)
    ⊢ refines top (PTXT' #true adv sym_scheme)
        (λ: "Q_enc" "Q_dec",
          (PTXT is_plaintext is_ciphertext elem_eq) #true
            (λ: "x", adv_PTXT' adv "x") sym_scheme "Q_enc" "Q_dec" "Q_dec")
        (lrel_int → lrel_int → lrel_bool).
  Proof with rel_pures_l; rel_pures_r.
    iIntros "#Hreladv".
    rewrite /PTXT/PTXT'...
    rel_arrow_val.
    iIntros (v1 v2 [Q_enc [eq1 eq2]]); subst...
    rel_arrow_val.
    iIntros (v1 v2 [Q_dec [eq1 eq2]]); subst...
    rel_apply refines_init_list_l.
    iIntros (lst) "Hlist".
    rel_apply refines_init_list_r.
    iIntros (lst') "Hlist'"...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP".
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rel_apply refines_sym_keygen_couple.
    iIntros (key) "#Hrelkey"...
    rewrite /q_calls_general_test...
    rel_alloc_l cnt_enc as "Hcnt_enc".
    rel_alloc_r cnt_enc' as "Hcnt_enc'"...
    rel_alloc_l cnt_lr as "Hcnt_lr".
    rewrite /q_calls_general_test_eager...
    rel_alloc_r cnt_dec' as "Hcnt_dec'"...
    rel_alloc_r cnt_lr' as "Hcnt_lr'"...
    rewrite /adv_PTXT'...
    rel_bind_l (adv _ _).
    rel_bind_r (adv _ _).
    rel_apply (refines_bind with "[-]").
    2: {
      iIntros (v v') "Hrelv"...
      rel_vals.
    }
    set (P := (∃ (q_enc q_dec : nat) (l l' : list val),
        linked_list  _ lst  l
      ∗ linked_slist _ lst' l'
      ∗ ForallSep2 (λ x y, lrel_msg x y) l l'
      ∗ ⌜length l = q_enc⌝
      ∗ cnt_enc  ↦  #q_enc
      ∗ cnt_enc' ↦ₛ #q_enc
      ∗ cnt_lr  ↦  #q_dec
      ∗ cnt_dec' ↦ₛ #q_dec
      ∗ cnt_lr' ↦ₛ #q_dec
      ∗ ⌜q_enc ≤ (Z.to_nat Q_enc)⌝
      ∗ ⌜q_dec ≤ (Z.to_nat Q_dec)⌝
    )%I).
    rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"PTXT'__PTXT_true".@"encryption")).
    iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'"). iIntros "#encInv".
    rel_apply (refines_na_alloc P (nroot.@"PTXT'__PTXT_true".@"oracles")).
    iSplitL.
    {
      iExists 0, 0.
      replace (Z.of_nat 0) with 0%Z by lia.
      iFrame. iModIntro.
      iPureIntro; repeat split; lia.
    }
    iIntros "#Inv".
    repeat rel_apply refines_app; first rel_vals.
    - rewrite /lrel_enc_oracle/symmetric_init.lrel_enc_oracle.
      rel_arrow_val.
      iIntros (msg1 msg2) "#Hrelmsg".
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      replace (msg1) with ((λ x, x) msg1) by done.
      replace (msg2) with ((λ x, x) msg2) by done.
      rel_apply refines_is_plaintext_l.
      { iExists msg2. iAssumption. }
      rel_apply refines_is_plaintext_r.
      { iExists msg1. iAssumption. }
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_enc < Q_enc)%Z) eqn:qltQenc...
      + rel_load_l; rel_load_r... rel_store_l; rel_store_r...
        replace (msg1) with (inject msg1) by reflexivity.
        rel_apply (refines_add_list_l with "[-Hlst]"); last iAssumption.
        iIntros "Hlst"...
        replace (msg2) with (inject msg2) by reflexivity.
        rel_apply (refines_add_list_r with "[-Hlst']"); last iAssumption.
        iIntros "Hlstr"...
        rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists (q_enc + 1), q_dec, (msg1 :: l), (msg2 :: l').
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia. iFrame.
          iSplitL; first iAssumption.
          apply bool_decide_eq_true in qltQenc.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; rewrite /P; iFrame.
        * rel_vals.
        * rel_vals.
      + rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists q_enc, q_dec, l, l'.
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_vals.
    - rel_arrow_val.
      iIntros (c1 c2) "#Hrelcipher"...
      rel_apply refines_is_ciphertext_l.
      { iExists c2; iAssumption. }
      rel_apply refines_is_ciphertext_r...
      { iExists c1; iAssumption. }
      rel_bind_l (sdec _ _ _).
      rel_bind_r (sdec _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        + rel_apply sdec_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      }
      iIntros (dec1 dec1') "#Hreldec1"...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_dec < Q_dec)%Z) eqn:qltQdec...
      + rel_load_l; rel_load_r; rel_store_l; rel_store_r...
        rel_apply refines_is_ciphertext_r...
        { iExists c1; iAssumption. }
        rel_load_r... rewrite qltQdec...
        rel_load_r; rel_store_r...
        rel_apply (refines_na_close); iFrame.
        iSplitL.
        {
          iModIntro. iExists (q_dec + 1).
          replace (Z.of_nat (q_dec + 1)) with (Z.of_nat q_dec + 1)%Z by lia.
          iFrame.
          apply bool_decide_eq_true in qltQdec.
          iPureIntro; repeat split; lia.
        }
        rel_bind_l (sdec _ _ _).
        rel_bind_r (sdec _ _ _).
        rel_apply refines_bind.
        {
          repeat rel_apply refines_app.
          + rel_apply sdec_sem_typed; last iApply "encInv".
            exists True%I. apply bi.equiv_entails. split;
            first iIntros "H"; last iIntros "[_ H]"; iFrame.
          + rel_vals.
          + rel_vals.
        }
        iIntros (dec2 dec2') "#Hreldec2".
        clear q_enc q_dec Hlen Hleqenc Hleqdec qltQdec l l'.
        rel_apply refines_na_inv; iSplitL; first iAssumption.
        iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
          [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec'
          [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
        epose proof (forall_lrel_pers l l' lrel_msg) as Hpers.
        apply persistent in Hpers.
        iPoseProof Hpers as "Hpers". clear Hpers.
        iPoseProof ("Hpers" with "Hll'") as "#Hl_l'". iClear "Hpers".
        iClear "Hll'".
        rel_apply (refines_elem_of_l with
          "[Hlst' Hcntenc Hcntenc' Hcntlr Hcntdec Hcntdec' Hclose] [Hlst] []").
        * iIntros (b) "Hlst %Hb". destruct b...
          ** rel_apply (refines_elem_of_r with
            "[Hlst Hcntenc Hcntenc' Hcntlr Hcntdec Hcntdec' Hclose] [Hlst'] []").
            ++ iIntros (b') "Hlst' %Hb'". destruct b'...
              -- rel_apply refines_na_close; iFrame; iSplitL.
                {
                  iExists _. iFrame. iSplit; first last.
                  - iPureIntro; repeat split.
                    + apply Hlen.
                    + lia.
                    + lia.
                  - iModIntro. iAssumption.  
                }
                rel_vals.
              -- assert (Hinl : dec2 ∈ l).
                { apply Hb. reflexivity. }
                assert (Hninl' : dec2' ∉ l').
                { intro G. apply Hb' in G. discriminate G. }
                clear Hb Hb'.
                iPoseProof (lrel_msg_eq dec2 dec2' with "Hreldec2") as "%Heqdec2".
                iPoseProof (in_forall2_in_l with "Hl_l'") as "Hin"; first apply Hinl.
                iDestruct "Hin" as (y) "[Hreldec2y %Hinl']".
                iPoseProof (lrel_msg_eq dec2 y with "Hreldec2y") as "%Heqdec2y".
                exfalso.
                apply Hninl'; subst.
                assumption.
            ++ iApply "Hlst'".
            ++ iClear "Inv encInv Hrelkey Hrelcipher Hreladv".
              clear -lrel_msg_comparable lrel_msg_eq. iSplit.
              {
                iRevert "Hl_l'". iRevert (l).
                iInduction l' as [|h' t'] "IHt'"; iIntros (l) "#Hrel_lst".
                - simpl. done.
                - destruct l as [|h t].
                  + iExFalso; iAssumption.
                  + simpl. iDestruct "Hrel_lst" as "[Hrel_head Hrel_tail]". iSplit.
                    * iRight. iExists h. iAssumption.
                    * iApply "IHt'". iModIntro. iAssumption.  
              }
              iRight. iExists dec2. iAssumption.
          ** rel_apply (refines_elem_of_r with
            "[Hlst Hcntenc Hcntenc' Hcntlr Hcntdec Hcntdec' Hclose] [Hlst'] []").
            ++ iIntros (b') "Hlst' %Hb'". destruct b'...
              -- assert (Hinl' : dec2' ∈ l').
                { apply Hb'. reflexivity. }
                assert (Hninl : dec2 ∉ l).
                { intro G. apply Hb in G. discriminate G. }
                clear Hb Hb'.
                iPoseProof (lrel_msg_eq dec2 dec2' with "Hreldec2") as "%Heqdec2".
                iPoseProof (in_forall2_in_r with "Hl_l'") as "Hin"; first apply Hinl'.
                iDestruct "Hin" as (x) "[Hreldec2x %Hinl]".
                iPoseProof (lrel_msg_eq x dec2' with "Hreldec2x") as "%Heqdec2x".
                exfalso.
                apply Hninl; subst.
                assumption.
              -- rel_apply refines_na_close; iFrame; iSplitL.
                {
                  iExists _. iFrame. iSplit; first last.
                  - iPureIntro; repeat split.
                    + apply Hlen.
                    + lia.
                    + lia.
                  - iModIntro. iAssumption.  
                }
                rel_vals.
            ++ iApply "Hlst'".
            ++ iClear "Inv encInv Hrelkey Hrelcipher Hreladv".
              clear -lrel_msg_comparable lrel_msg_eq. iSplit.
              {
                iRevert "Hl_l'". iRevert (l).
                iInduction l' as [|h' t'] "IHt'"; iIntros (l) "#Hrel_lst".
                - simpl. done.
                - destruct l as [|h t].
                  + iExFalso; iAssumption.
                  + simpl. iDestruct "Hrel_lst" as "[Hrel_head Hrel_tail]". iSplit.
                    * iRight. iExists h. iAssumption.
                    * iApply "IHt'". iModIntro. iAssumption.  
              }
              iRight. iExists dec2. iAssumption.
        * iAssumption.
        * iClear "Inv encInv Hrelkey Hrelcipher Hreladv".
          clear -lrel_msg_comparable lrel_msg_eq. iSplit.
          {
            iRevert "Hl_l'". iRevert (l').
            iInduction l as [|h t] "IHt'"; iIntros (l') "#Hrel_lst".
            - simpl. done.
            - destruct l' as [|h' t'].
              + iExFalso; iAssumption.
              + simpl. iDestruct "Hrel_lst" as "[Hrel_head Hrel_tail]". iSplit.
                * iLeft. iExists h'. iAssumption.
                * iApply "IHt'". iModIntro. iAssumption.  
          }
          iLeft. iExists dec2'. iAssumption.
      + rel_apply refines_is_ciphertext_r...
        { iExists c1; iAssumption. }
        rel_load_r... rewrite qltQdec...
        rel_apply refines_na_close; iFrame.
        iSplit.
        { iPureIntro; repeat split; lia. }
        rel_vals.
  Qed.

  Lemma dec__ideal_dec_true (adv : val) :
      ((lrel_car (lrel_enc_oracle → lrel_dec_oracle → lrel_bool)) adv adv)
    ⊢ refines top
        (λ: "Q_enc" "Q_dec",
          (PTXT is_plaintext is_ciphertext elem_eq) #true
            (λ: "x", adv_PTXT' adv "x") sym_scheme "Q_enc" "Q_dec" "Q_dec")
        (PTXT' #true adv sym_scheme)
        (lrel_int → lrel_int → lrel_bool).
  Proof with rel_pures_l; rel_pures_r.
    iIntros "#Hreladv".
    rewrite /PTXT/PTXT'...
    rel_arrow_val.
    iIntros (v1 v2 [Q_enc [eq1 eq2]]); subst...
    rel_arrow_val.
    iIntros (v1 v2 [Q_dec [eq1 eq2]]); subst...
    rel_apply refines_init_list_l.
    iIntros (lst) "Hlist".
    rel_apply refines_init_list_r.
    iIntros (lst') "Hlist'"...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP".
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rel_apply refines_sym_keygen_couple.
    iIntros (key) "#Hrelkey"...
    rewrite /q_calls_general_test...
    rel_alloc_l cnt_enc as "Hcnt_enc".
    rel_alloc_r cnt_enc' as "Hcnt_enc'"...
    rel_alloc_r cnt_lr' as "Hcnt_lr'".
    rewrite /q_calls_general_test_eager...
    rel_alloc_l cnt_dec as "Hcnt_dec"...
    rel_alloc_l cnt_lr as "Hcnt_lr"...
    rewrite /adv_PTXT'...
    rel_bind_l (adv _ _).
    rel_bind_r (adv _ _).
    rel_apply (refines_bind with "[-]").
    2: {
      iIntros (v v') "Hrelv"...
      rel_vals.
    }
    set (P := (∃ (q_enc q_dec : nat) (l l' : list val),
        linked_list  _ lst  l
      ∗ linked_slist _ lst' l'
      ∗ ForallSep2 (λ x y, lrel_msg x y) l l'
      ∗ ⌜length l = q_enc⌝
      ∗ cnt_enc'  ↦ₛ  #q_enc
      ∗ cnt_enc ↦ #q_enc
      ∗ cnt_lr'  ↦ₛ  #q_dec
      ∗ cnt_dec ↦ #q_dec
      ∗ cnt_lr ↦ #q_dec
      ∗ ⌜q_enc ≤ (Z.to_nat Q_enc)⌝
      ∗ ⌜q_dec ≤ (Z.to_nat Q_dec)⌝
    )%I).
    rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"PTXT'__PTXT_true".@"encryption")).
    iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'"). iIntros "#encInv".
    rel_apply (refines_na_alloc P (nroot.@"PTXT'__PTXT_true".@"oracles")).
    iSplitL.
    {
      iExists 0, 0.
      replace (Z.of_nat 0) with 0%Z by lia.
      iFrame. iModIntro.
      iPureIntro; repeat split; lia.
    }
    iIntros "#Inv".
    repeat rel_apply refines_app; first rel_vals.
    - rewrite /lrel_enc_oracle/symmetric_init.lrel_enc_oracle.
      rel_arrow_val.
      iIntros (msg1 msg2) "#Hrelmsg".
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      replace (msg1) with ((λ x, x) msg1) by done.
      replace (msg2) with ((λ x, x) msg2) by done.
      rel_apply refines_is_plaintext_l.
      { iExists msg2. iAssumption. }
      rel_apply refines_is_plaintext_r.
      { iExists msg1. iAssumption. }
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_enc < Q_enc)%Z) eqn:qltQenc...
      + rel_load_l; rel_load_r... rel_store_l; rel_store_r...
        replace (msg1) with (inject msg1) by reflexivity.
        rel_apply (refines_add_list_l with "[-Hlst]"); last iAssumption.
        iIntros "Hlst"...
        replace (msg2) with (inject msg2) by reflexivity.
        rel_apply (refines_add_list_r with "[-Hlst']"); last iAssumption.
        iIntros "Hlstr"...
        rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists (q_enc + 1), q_dec, (msg1 :: l), (msg2 :: l').
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia. iFrame.
          iSplitL; first iAssumption.
          apply bool_decide_eq_true in qltQenc.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; rewrite /P; iFrame.
        * rel_vals.
        * rel_vals.
      + rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists q_enc, q_dec, l, l'.
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_vals.
    - rel_arrow_val.
      iIntros (c1 c2) "#Hrelcipher"...
      rel_apply refines_is_ciphertext_l.
      { iExists c2; iAssumption. }
      rel_apply refines_is_ciphertext_r...
      { iExists c1; iAssumption. }
      rel_bind_l (sdec _ _ _).
      rel_bind_r (sdec _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        + rel_apply sdec_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      }
      iIntros (dec1 dec1') "#Hreldec1"...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_dec < Q_dec)%Z) eqn:qltQdec...
      + rel_load_l; rel_load_r; rel_store_l; rel_store_r...
        rel_apply refines_is_ciphertext_l...
        { iExists c2; iAssumption. }
        rel_load_l... rewrite qltQdec...
        rel_load_l; rel_store_l...
        rel_apply (refines_na_close); iFrame.
        iSplitL.
        {
          iModIntro. iExists (q_dec + 1).
          replace (Z.of_nat (q_dec + 1)) with (Z.of_nat q_dec + 1)%Z by lia.
          iFrame.
          apply bool_decide_eq_true in qltQdec.
          iPureIntro; repeat split; lia.
        }
        rel_bind_l (sdec _ _ _).
        rel_bind_r (sdec _ _ _).
        rel_apply refines_bind.
        {
          repeat rel_apply refines_app.
          + rel_apply sdec_sem_typed; last iApply "encInv".
            exists True%I. apply bi.equiv_entails. split;
            first iIntros "H"; last iIntros "[_ H]"; iFrame.
          + rel_vals.
          + rel_vals.
        }
        iIntros (dec2 dec2') "#Hreldec2".
        clear q_enc q_dec Hlen Hleqenc Hleqdec qltQdec l l'.
        rel_apply refines_na_inv; iSplitL; first iAssumption.
        iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
          [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec'
          [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
        epose proof (forall_lrel_pers l l' lrel_msg) as Hpers.
        apply persistent in Hpers.
        iPoseProof Hpers as "Hpers". clear Hpers.
        iPoseProof ("Hpers" with "Hll'") as "#Hl_l'". iClear "Hpers".
        iClear "Hll'".
        rel_apply (refines_elem_of_l with
          "[Hlst' Hcntenc Hcntenc' Hcntlr Hcntdec Hcntdec' Hclose] [Hlst] []").
        * iIntros (b) "Hlst %Hb". destruct b...
          ** rel_apply (refines_elem_of_r with
            "[Hlst Hcntenc Hcntenc' Hcntlr Hcntdec Hcntdec' Hclose] [Hlst'] []").
            ++ iIntros (b') "Hlst' %Hb'". destruct b'...
              -- rel_apply refines_na_close; iFrame; iSplitL.
                {
                  iExists _. iFrame. iSplit; first last.
                  - iPureIntro; repeat split.
                    + apply Hlen.
                    + lia.
                    + lia.
                  - iModIntro. iAssumption.  
                }
                rel_vals.
              -- assert (Hinl : dec2 ∈ l).
                { apply Hb. reflexivity. }
                assert (Hninl' : dec2' ∉ l').
                { intro G. apply Hb' in G. discriminate G. }
                clear Hb Hb'.
                iPoseProof (lrel_msg_eq dec2 dec2' with "Hreldec2") as "%Heqdec2".
                iPoseProof (in_forall2_in_l with "Hl_l'") as "Hin"; first apply Hinl.
                iDestruct "Hin" as (y) "[Hreldec2y %Hinl']".
                iPoseProof (lrel_msg_eq dec2 y with "Hreldec2y") as "%Heqdec2y".
                exfalso.
                apply Hninl'; subst.
                assumption.
            ++ iApply "Hlst'".
            ++ iClear "Inv encInv Hrelkey Hrelcipher Hreladv".
              clear -lrel_msg_comparable lrel_msg_eq. iSplit.
              {
                iRevert "Hl_l'". iRevert (l).
                iInduction l' as [|h' t'] "IHt'"; iIntros (l) "#Hrel_lst".
                - simpl. done.
                - destruct l as [|h t].
                  + iExFalso; iAssumption.
                  + simpl. iDestruct "Hrel_lst" as "[Hrel_head Hrel_tail]". iSplit.
                    * iRight. iExists h. iAssumption.
                    * iApply "IHt'". iModIntro. iAssumption.  
              }
              iRight. iExists dec2. iAssumption.
          ** rel_apply (refines_elem_of_r with
            "[Hlst Hcntenc Hcntenc' Hcntlr Hcntdec Hcntdec' Hclose] [Hlst'] []").
            ++ iIntros (b') "Hlst' %Hb'". destruct b'...
              -- assert (Hinl' : dec2' ∈ l').
                { apply Hb'. reflexivity. }
                assert (Hninl : dec2 ∉ l).
                { intro G. apply Hb in G. discriminate G. }
                clear Hb Hb'.
                iPoseProof (lrel_msg_eq dec2 dec2' with "Hreldec2") as "%Heqdec2".
                iPoseProof (in_forall2_in_r with "Hl_l'") as "Hin"; first apply Hinl'.
                iDestruct "Hin" as (x) "[Hreldec2x %Hinl]".
                iPoseProof (lrel_msg_eq x dec2' with "Hreldec2x") as "%Heqdec2x".
                exfalso.
                apply Hninl; subst.
                assumption.
              -- rel_apply refines_na_close; iFrame; iSplitL.
                {
                  iExists _. iFrame. iSplit; first last.
                  - iPureIntro; repeat split.
                    + apply Hlen.
                    + lia.
                    + lia.
                  - iModIntro. iAssumption.  
                }
                rel_vals.
            ++ iApply "Hlst'".
            ++ iClear "Inv encInv Hrelkey Hrelcipher Hreladv".
              clear -lrel_msg_comparable lrel_msg_eq. iSplit.
              {
                iRevert "Hl_l'". iRevert (l).
                iInduction l' as [|h' t'] "IHt'"; iIntros (l) "#Hrel_lst".
                - simpl. done.
                - destruct l as [|h t].
                  + iExFalso; iAssumption.
                  + simpl. iDestruct "Hrel_lst" as "[Hrel_head Hrel_tail]". iSplit.
                    * iRight. iExists h. iAssumption.
                    * iApply "IHt'". iModIntro. iAssumption.  
              }
              iRight. iExists dec2. iAssumption.
        * iAssumption.
        * iClear "Inv encInv Hrelkey Hrelcipher Hreladv".
          clear -lrel_msg_comparable lrel_msg_eq. iSplit.
          {
            iRevert "Hl_l'". iRevert (l').
            iInduction l as [|h t] "IHt'"; iIntros (l') "#Hrel_lst".
            - simpl. done.
            - destruct l' as [|h' t'].
              + iExFalso; iAssumption.
              + simpl. iDestruct "Hrel_lst" as "[Hrel_head Hrel_tail]". iSplit.
                * iLeft. iExists h'. iAssumption.
                * iApply "IHt'". iModIntro. iAssumption.  
          }
          iLeft. iExists dec2'. iAssumption.
      + rel_apply refines_is_ciphertext_l...
        { iExists c2; iAssumption. }
        rel_load_l... rewrite qltQdec...
        rel_apply refines_na_close; iFrame.
        iSplit.
        { iPureIntro; repeat split; lia. }
        rel_vals.
  Qed.

  Lemma dec_ideal__dec_false (adv : val) :
      ((lrel_car (lrel_enc_oracle → lrel_dec_oracle → lrel_bool)) adv adv)
    ⊢ refines top (PTXT' #false adv sym_scheme)
        (λ: "Q_enc" "Q_dec",
          (PTXT is_plaintext is_ciphertext elem_eq) #false
            (λ: "x", adv_PTXT' adv "x") sym_scheme "Q_enc" "Q_dec" "Q_dec")
        (lrel_int → lrel_int → lrel_bool).
  Proof with rel_pures_l; rel_pures_r.
    iIntros "#Hreladv".
    rewrite /PTXT/PTXT'...
    rel_arrow_val.
    iIntros (v1 v2 [Q_enc [eq1 eq2]]); subst...
    rel_arrow_val.
    iIntros (v1 v2 [Q_dec [eq1 eq2]]); subst...
    rel_apply refines_init_list_l.
    iIntros (lst) "Hlist".
    rel_apply refines_init_list_r.
    iIntros (lst') "Hlist'"...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP".
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rel_apply refines_sym_keygen_couple.
    iIntros (key) "#Hrelkey"...
    rewrite /q_calls_general_test...
    rel_alloc_l cnt_enc as "Hcnt_enc".
    rel_alloc_r cnt_enc' as "Hcnt_enc'"...
    rel_alloc_l cnt_lr as "Hcnt_lr".
    rewrite /q_calls_general_test_eager...
    rel_alloc_r cnt_dec' as "Hcnt_dec'"...
    rel_alloc_r cnt_lr' as "Hcnt_lr'"...
    rewrite /adv_PTXT'...
    rel_bind_l (adv _ _).
    rel_bind_r (adv _ _).
    rel_apply (refines_bind with "[-]").
    2: {
      iIntros (v v') "Hrelv"...
      rel_vals.
    }
    set (P := (∃ (q_enc q_dec : nat) (l l' : list val),
        linked_list  _ lst  l
      ∗ linked_slist _ lst' l'
      ∗ ForallSep2 (λ x y, lrel_msg x y) l l'
      ∗ ⌜length l = q_enc⌝
      ∗ cnt_enc  ↦  #q_enc
      ∗ cnt_enc' ↦ₛ #q_enc
      ∗ cnt_lr  ↦  #q_dec
      ∗ cnt_dec' ↦ₛ #q_dec
      ∗ cnt_lr' ↦ₛ #q_dec
      ∗ ⌜q_enc ≤ (Z.to_nat Q_enc)⌝
      ∗ ⌜q_dec ≤ (Z.to_nat Q_dec)⌝
    )%I).
    rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"PTXT'__PTXT_true".@"encryption")).
    iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'"). iIntros "#encInv".
    rel_apply (refines_na_alloc P (nroot.@"PTXT'__PTXT_true".@"oracles")).
    iSplitL.
    {
      iExists 0, 0.
      replace (Z.of_nat 0) with 0%Z by lia.
      iFrame. iModIntro.
      iPureIntro; repeat split; lia.
    }
    iIntros "#Inv".
    repeat rel_apply refines_app; first rel_vals.
    - rewrite /lrel_enc_oracle/symmetric_init.lrel_enc_oracle.
      rel_arrow_val.
      iIntros (msg1 msg2) "#Hrelmsg".
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      replace (msg1) with ((λ x, x) msg1) by done.
      replace (msg2) with ((λ x, x) msg2) by done.
      rel_apply refines_is_plaintext_l.
      { iExists msg2. iAssumption. }
      rel_apply refines_is_plaintext_r.
      { iExists msg1. iAssumption. }
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_enc < Q_enc)%Z) eqn:qltQenc...
      + rel_load_l; rel_load_r... rel_store_l; rel_store_r...
        replace (msg1) with (inject msg1) by reflexivity.
        rel_apply (refines_add_list_l with "[-Hlst]"); last iAssumption.
        iIntros "Hlst"...
        replace (msg2) with (inject msg2) by reflexivity.
        rel_apply (refines_add_list_r with "[-Hlst']"); last iAssumption.
        iIntros "Hlstr"...
        rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists (q_enc + 1), q_dec, (msg1 :: l), (msg2 :: l').
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia. iFrame.
          iSplitL; first iAssumption.
          apply bool_decide_eq_true in qltQenc.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; rewrite /P; iFrame.
        * rel_vals.
        * rel_vals.
      + rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists q_enc, q_dec, l, l'.
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_vals.
    - rel_arrow_val.
      iIntros (c1 c2) "#Hrelcipher"...
      rel_apply refines_is_ciphertext_l.
      { iExists c2; iAssumption. }
      rel_apply refines_is_ciphertext_r...
      { iExists c1; iAssumption. }
      rel_bind_l (sdec _ _ _).
      rel_bind_r (sdec _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        + rel_apply sdec_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      }
      iIntros (dec1 dec1') "#Hreldec1"...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_dec < Q_dec)%Z) eqn:qltQdec...
      + rel_load_l; rel_load_r; rel_store_l; rel_store_r...
        rel_apply refines_is_ciphertext_r...
        { iExists c1; iAssumption. }
        rel_load_r... rewrite qltQdec...
        rel_load_r; rel_store_r...
        rel_apply (refines_na_close); iFrame.
        iSplitL.
        {
          iModIntro. iExists (q_dec + 1).
          replace (Z.of_nat (q_dec + 1)) with (Z.of_nat q_dec + 1)%Z by lia.
          iFrame.
          apply bool_decide_eq_true in qltQdec.
          iPureIntro; repeat split; lia.
        }
        rel_vals.
      + rel_apply refines_is_ciphertext_r...
        { iExists c1; iAssumption. }
        rel_load_r... rewrite qltQdec...
        rel_apply refines_na_close; iFrame.
        iSplit.
        { iPureIntro; repeat split; lia. }
        rel_vals.
  Qed.

  Lemma dec__dec_ideal_false (adv : val) :
      ((lrel_car (lrel_enc_oracle → lrel_dec_oracle → lrel_bool)) adv adv)
    ⊢ refines top
        (λ: "Q_enc" "Q_dec",
          (PTXT is_plaintext is_ciphertext elem_eq) #false
            (λ: "x", adv_PTXT' adv "x") sym_scheme "Q_enc" "Q_dec" "Q_dec")
        (PTXT' #false adv sym_scheme)
        (lrel_int → lrel_int → lrel_bool).
  Proof with rel_pures_l; rel_pures_r.
    iIntros "#Hreladv".
    rewrite /PTXT/PTXT'...
    rel_arrow_val.
    iIntros (v1 v2 [Q_enc [eq1 eq2]]); subst...
    rel_arrow_val.
    iIntros (v1 v2 [Q_dec [eq1 eq2]]); subst...
    rel_apply refines_init_list_l.
    iIntros (lst) "Hlist".
    rel_apply refines_init_list_r.
    iIntros (lst') "Hlist'"...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP".
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rel_apply refines_sym_keygen_couple.
    iIntros (key) "#Hrelkey"...
    rewrite /q_calls_general_test...
    rel_alloc_r cnt_enc' as "Hcnt_enc'".
    rel_alloc_l cnt_enc as "Hcnt_enc"...
    rel_alloc_r cnt_lr' as "Hcnt_lr'".
    rewrite /q_calls_general_test_eager...
    rel_alloc_l cnt_dec as "Hcnt_dec"...
    rel_alloc_l cnt_lr as "Hcnt_lr"...
    rewrite /adv_PTXT'...
    rel_bind_l (adv _ _).
    rel_bind_r (adv _ _).
    rel_apply (refines_bind with "[-]").
    2: {
      iIntros (v v') "Hrelv"...
      rel_vals.
    }
    set (P := (∃ (q_enc q_dec : nat) (l l' : list val),
        linked_list  _ lst  l
      ∗ linked_slist _ lst' l'
      ∗ ForallSep2 (λ x y, lrel_msg x y) l l'
      ∗ ⌜length l = q_enc⌝
      ∗ cnt_enc'  ↦ₛ  #q_enc
      ∗ cnt_enc ↦ #q_enc
      ∗ cnt_lr'  ↦ₛ  #q_dec
      ∗ cnt_dec ↦ #q_dec
      ∗ cnt_lr ↦ #q_dec
      ∗ ⌜q_enc ≤ (Z.to_nat Q_enc)⌝
      ∗ ⌜q_dec ≤ (Z.to_nat Q_dec)⌝
    )%I).
    rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"PTXT'__PTXT_true".@"encryption")).
    iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'"). iIntros "#encInv".
    rel_apply (refines_na_alloc P (nroot.@"PTXT'__PTXT_true".@"oracles")).
    iSplitL.
    {
      iExists 0, 0.
      replace (Z.of_nat 0) with 0%Z by lia.
      iFrame. iModIntro.
      iPureIntro; repeat split; lia.
    }
    iIntros "#Inv".
    repeat rel_apply refines_app; first rel_vals.
    - rewrite /lrel_enc_oracle/symmetric_init.lrel_enc_oracle.
      rel_arrow_val.
      iIntros (msg1 msg2) "#Hrelmsg".
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      replace (msg1) with ((λ x, x) msg1) by done.
      replace (msg2) with ((λ x, x) msg2) by done.
      rel_apply refines_is_plaintext_l.
      { iExists msg2. iAssumption. }
      rel_apply refines_is_plaintext_r.
      { iExists msg1. iAssumption. }
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_enc < Q_enc)%Z) eqn:qltQenc...
      + rel_load_l; rel_load_r... rel_store_l; rel_store_r...
        replace (msg1) with (inject msg1) by reflexivity.
        rel_apply (refines_add_list_l with "[-Hlst]"); last iAssumption.
        iIntros "Hlst"...
        replace (msg2) with (inject msg2) by reflexivity.
        rel_apply (refines_add_list_r with "[-Hlst']"); last iAssumption.
        iIntros "Hlstr"...
        rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists (q_enc + 1), q_dec, (msg1 :: l), (msg2 :: l').
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia. iFrame.
          iSplitL; first iAssumption.
          apply bool_decide_eq_true in qltQenc.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; rewrite /P; iFrame.
        * rel_vals.
        * rel_vals.
      + rel_apply refines_na_close.
        iSplitR "Hclose"; last (iSplitL; first iAssumption).
        {
          iExists q_enc, q_dec, l, l'.
          iModIntro. iFrame.
          replace (Z.of_nat (q_enc + 1)) with (q_enc + 1)%Z by lia.
          repeat iSplit; iPureIntro; simpl; lia.
        }
        rel_vals.
    - rel_arrow_val.
      iIntros (c1 c2) "#Hrelcipher"...
      rel_apply refines_is_ciphertext_l.
      { iExists c2; iAssumption. }
      rel_apply refines_is_ciphertext_r...
      { iExists c1; iAssumption. }
      rel_bind_l (sdec _ _ _).
      rel_bind_r (sdec _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        + rel_apply sdec_sem_typed; last iApply "encInv".
          exists True%I. apply bi.equiv_entails. split;
          first iIntros "H"; last iIntros "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      }
      iIntros (dec1 dec1') "#Hreldec1"...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%q_enc [%q_dec [%l [%l' [Hlst [Hlst' [Hll' >[%Hlen
        [Hcntenc [Hcntenc' [Hcntlr [Hcntdec [Hcntdec' [%Hleqenc %Hleqdec]]]]]]]]]]]]]] Hclose]"...
      rel_load_l; rel_load_r...
      destruct (bool_decide (q_dec < Q_dec)%Z) eqn:qltQdec...
      + rel_load_l; rel_load_r; rel_store_l; rel_store_r...
        rel_apply refines_is_ciphertext_l...
        { iExists c2; iAssumption. }
        rel_load_l... rewrite qltQdec...
        rel_load_l; rel_store_l...
        rel_apply (refines_na_close); iFrame.
        iSplitL.
        {
          iModIntro. iExists (q_dec + 1).
          replace (Z.of_nat (q_dec + 1)) with (Z.of_nat q_dec + 1)%Z by lia.
          iFrame.
          apply bool_decide_eq_true in qltQdec.
          iPureIntro; repeat split; lia.
        }
        rel_vals.
      + rel_apply refines_is_ciphertext_l...
        { iExists c2; iAssumption. }
        rel_load_l... rewrite qltQdec...
        rel_apply refines_na_close; iFrame.
        iSplit.
        { iPureIntro; repeat split; lia. }
        rel_vals.
  Qed.

End logrel.
