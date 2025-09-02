From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.approxis Require Import map reltac2 approxis option linked_list.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init
  advantage_laws iterable_expression.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section logrel.
  
  Context `{!approxisRGS Σ}.

  Variable lrel_msg : lrel Σ.
  Variable lrel_cipher : lrel Σ.
  Variable lrel_key : lrel Σ.

  Variable is_key : val.
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

  Definition CTXT : val :=
    λ: "b" "adv" "scheme" "Q_enc" "Q_dec" "Q_lr" "Q_enc_gen",
      let: "record_cipher" := init_linked_list #() in
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "enc" := get_enc "enc_scheme" in
      let: "dec" := get_dec "enc_scheme" in
      let: "key" := get_keygen "scheme" #() in
      let: "enc_key" := λ: "msg", add_list "record_cipher" "msg";;
        "enc" "key" "msg" in
      (* FIXME maybe record when called with a valid guess of key *)
      let: "oracle_enc_gen" :=
        q_calls_general_test
          (λ: "p", is_key (Fst "p") `and` is_plaintext (Snd "p"))
          "Q_enc"
          (λ: "p", "enc" (Fst "p") (Snd "p")) in
      let: "oracle_enc_gen_curry" :=
        λ: "k" "msg", "oracle_enc_gen" ("k", "msg") in
      let: "dec_key" := λ: "msg", "dec" "key" "msg" in
      let: "rr_key_b" :=
        if: "b" then
          λ: "c", elem_of_linked_list elem_eq "record_cipher" "c"
        else
          λ: <>, #true in
      let: "oracle_enc_key" :=
        q_calls_general_test is_plaintext "Q_enc" "enc_key" in
      let: "oracle_dec" :=
        q_calls_general_test_eager is_ciphertext "Q_dec" "dec_key" in
      let: "oracle_lr" :=
        q_calls_general_test is_ciphertext "Q_lr" "rr_key_b" in
      let: "b'" := "adv" "oracle_enc_gen_curry"
        "oracle_enc_key" "oracle_dec" "oracle_lr" in
      "b'".

  Definition CTXT' : val :=
    λ: "b" "adv" "scheme" "Q_enc" "Q_dec" "Q_lr" "Q_enc_gen",
      let: "record" := init_map #() in
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "enc" := get_enc "enc_scheme" in
      let: "dec" := get_dec "enc_scheme" in
      let: "key" := get_keygen "scheme" #() in
      let: "enc_key" := λ: "msg",
        let: "c" := "enc" "key" "msg" in
        set "record" "c" "msg"
        in
      (* FIXME maybe record when called with a valid guess of key *)
      let: "oracle_enc_gen" :=
        q_calls_general_test
          (λ: "p", is_key (Fst "p") `and` is_plaintext (Snd "p"))
          "Q_enc"
          (λ: "p", "enc" (Fst "p") (Snd "p")) in
      let: "oracle_enc_gen_curry" :=
        λ: "k" "msg", "oracle_enc_gen" ("k", "msg") in
      let: "dec_key" :=
        if: "b" then
          λ: "c", "dec" "key" "c"
        else
          λ: "c",
            "get" "record" "c"
        in
      let: "rr_key_b" :=
        if: "b" then
          λ: "c", elem_of_linked_list elem_eq "record" "c"
        else
          λ: <>, #true in

      let: "oracle_enc_key" :=
        q_calls_general_test is_plaintext "Q_enc" "enc_key" in
      let: "oracle_dec" :=
        q_calls_general_test_eager is_ciphertext "Q_dec" "dec_key" in
      let: "oracle_lr" :=
        q_calls_general_test is_ciphertext "Q_lr" "rr_key_b" in
      let: "b'" := "adv" "oracle_enc_gen_curry"
        "oracle_enc_key" "oracle_dec" "oracle_lr" in
      "b'".

  Definition adv_CTXT' : val :=
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

End logrel.
