From clutch.prob_eff_lang.probblaze Require Import notation logic sem_judgement sem_types sem_def tactics proofmode.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.examples Require Import fin_val_type.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_finval.
Set Default Proof Using "Type*".

Section symmetric.

  (** A symmetric encryption [scheme] is given by three functions (encrypt, decrypt). *)

  Definition rand_fvt `(s : fin_val_type_struct) : val :=
    λ: <>, match: s.(fvt_of_int) (rand #(Z.to_nat (s.(card) - 1))) with
             NONE     => #()%V  (* dead branch that cannot be reached *)
           | SOME "x" => "x"
           end.

  Class SYM_struct 
    `{ks : fin_val_type_struct}
    `{ms : fin_val_type_struct}
    `{cs : fin_val_type_struct} :=
    { enc : val
    ; dec : val
    ; enc_closed : is_closed_val enc
    ; dec_closed : is_closed_val dec
    ; ms_inhabited :: Inhabited (fvt_sort ms)
    ; cs_inhabited :: Inhabited (fvt_sort cs)
    ; ks_inhabited :: Inhabited (fvt_sort ks)
    ; rand_cipher : val := rand_fvt cs
    ; rand_key : val := rand_fvt ks
    }.

  Class SYM `{HΣ : probblazeRGS Σ}
    {kt mt ct : fin_val_type}
    {ks : @fin_val_type_struct kt}
    {ms : @fin_val_type_struct mt}
    {cs : @fin_val_type_struct ct}
    {key    : @fin_val Σ HΣ _ ks}
    {msg    : @fin_val Σ HΣ _ ms}
    {cipher : @fin_val Σ HΣ _ cs}
    {sym_struct : @SYM_struct _ ks _ ms _ cs} :=
    { P : key → msg → cipher → iProp Σ
    ; P_pers k m c :: Persistent (P k m c)
    ; brel_enc_couple : ∀ (k : key) (m : msg),
        ⊢ BREL (enc (fvtval k) (fvtval m)) ≤ enc (fvtval k) (fvtval m) <|⊥|> {{ (λ v1 v2, ∃ c : cipher, ⌜v1 = fvtval c⌝ ∗ ⌜v2 = fvtval c⌝ ∗ (P k m c)) }}
    ; brel_dec_enc_correct_l : ∀ (k : key) (m : msg) (c : cipher) K e E X R,
        P k m c -∗ 
        BREL fill K (SOMEV (fvtval m)) ≤ e @ E <|X|> {{ R }} -∗ 
        BREL fill K (dec (fvtval k) (fvtval c)) ≤ e @ E <|X|> {{ R }}
    ; brel_dec_enc_correct_r : ∀ (k : key) (m : msg) (c : cipher) K e E X R,
        P k m c -∗ 
        BREL e ≤ fill K (SOMEV (fvtval m)) @ E <|X|> {{ R }} -∗ 
        BREL e ≤ fill K (dec (fvtval k) (fvtval c)) @ E <|X|> {{ R }}
    ; dec_typed : ⊢ ⊨ᵥ dec ≤ dec : (key.(sem_τFT) -{ ⊥ }-> cipher.(sem_τFT) -{ ⊥ }-> Option msg.(sem_τFT))
    ; kt_nontrivial : (2 ≤ kt.(card))%nat
    ; cs_nontrivial : (2 ≤ ct.(card))%nat
    }.

  Definition sym_struct_of_sym := λ {Σ} {HΣ} kt mt ct ks ms cs (key : @fin_val Σ HΣ kt ks) (msg : @fin_val Σ HΣ mt ms) (cipher : @fin_val Σ HΣ ct cs) (sym_struct : @SYM_struct kt ks mt ms ct cs) (sym : @SYM Σ HΣ kt mt ct ks ms cs key msg cipher sym_struct), sym_struct.
  Coercion sym_struct_of_sym : SYM >-> SYM_struct.

  Lemma rand_cipher_coupl `{SYM} E K K' X R :
    (∀ c : cipher, BREL fill K (fvtval c) ≤ fill K' (fvtval c) @ E <|X|> {{R}}) -∗
    BREL fill K (rand_cipher #()%V) ≤ fill K' (rand_cipher #()%V) @ E <|X|> {{R}}.
  Proof.
    iIntros "Hkont".
    rewrite /rand_cipher /rand_fvt /=.
    brel_pures_l.
    brel_pures_r.
    iApply brel_couple_rand_rand; first done.
    iIntros (c) "%Hlt".
    rewrite !fill_app /=. 
    apply Nat.lt_succ_r in Hlt.
    unfold fvt_of_fvts in Hlt.
    pose proof cs_nontrivial as Hnt.
    destruct (fvt_of_int_sem_surj (FV := cipher) c) as (x & Hx & _); first lia.
    iApply brel_fvt_of_int_correct_l; first done.
    iApply brel_fvt_of_int_correct_r; first done.
    rewrite !fill_app /=. 
    brel_pures_l.
    brel_pures_r.
    by iApply "Hkont".
  Qed.

End symmetric.

#[export] Hint Resolve enc_closed : core.
#[export] Hint Resolve dec_closed : core.

Section programs.
  Context `{sym_struct : SYM_struct}.

  Definition enc_real_tape : val :=
    λ: <>, let: "ι" := alloc #(ks.(card) - 1) in
      λ: "m", let: "n" := rand("ι") #(Z.to_nat (ks.(card) - 1)) in
              match: ks.(fvt_of_int) "n" with
                NONE     => fvtval (inhabitant : fvt_sort cs)
              | SOME "k" => enc "k" "m"
              end.

  Definition enc_real : val :=
    λ: <> "m", let: "k" := rand_key #()%V in enc "k" "m".

  Definition enc_ideal : val := λ: <> "m", rand_cipher #()%V.

End programs.

#[global] Arguments enc_real_tape {_ _ _ _ _ _} _.
#[global] Arguments enc_real      {_ _ _ _ _ _} _.
#[global] Arguments enc_ideal     {_ _ _ _ _ _} _.

From clutch.prob_eff_lang.probblaze Require Import sem_row compatibility.

Section OTS.
  Context `{ske : SYM}.

  (* [rand_cipher_coupl] in the logic for equivalences. *)
  Lemma eq_rand_cipher_coupl E K K' (X : eqThy _) R :
    (∀ c : cipher, EQ fill K (fvtval c) ≈ fill K' (fvtval c) @ E <|X|> {{ R }})
    ⊢ EQ fill K (rand_cipher #()%V) ≈ fill K' (rand_cipher #()%V) @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_forall eq_rel_at. iIntros "H".
    destruct d; rewrite /pick /=; iApply (rand_cipher_coupl (H := ske)); iIntros (c); iSpecialize ("H" $! c);
      [iApply (eq_rel_at_elim Fwd)|iApply (eq_rel_at_elim Bwd)]; iApply "H".
  Qed.

  Lemma enc_real_tape_EQ :
    ⊢ EQ enc_real_tape ske ≈ enc_real ske <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ 𝟙 -{ ⟨⟩ }-[ MS ]-> (msg.(sem_τFT) → cipher.(sem_τFT)) ⟫ }}.
  Proof.
    rewrite /enc_real_tape /enc_real.
    iApply eq_value. iModIntro. iModIntro. iApply eq_lift_arr. iIntros (u1 u2) "Hu".
    rewrite eq_lift_unit. iDestruct "Hu" as %[-> ->].
    eq_pures_l. eq_pures_r.
    eq_alloctape_l ι as "Hι".
    iApply (eq_na_alloc (ι ↪ₗN (Z.to_nat (key.(card) - 1); [])) (nroot .@ "inv")).
    iSplitL "Hι"; first by iFrame.
    iIntros "#HI". eq_pures_l.
    iApply eq_value. iModIntro. iModIntro.
    iApply eq_lift_arr. iIntros (m1 m2) "Hm". rewrite eq_lift_fvt. iDestruct "Hm" as %(m & -> & ->).
    iApply (eq_na_open _ _ (nroot .@ "inv")); first solve_ndisj.
    iFrame "HI". iIntros "[>Hι Hclose]".
    eq_pures_l. eq_pures_r.
    rewrite /rand_key /rand_fvt. eq_pures_r.
    eq_couple_tape_rand "Hι". iIntros (n Hn) "Hι /=".
    eq_rand_l as "_". eq_pures_l.
    iApply eq_na_close_rule. iFrame "Hclose Hι".
    pose proof kt_nontrivial as Hnt.
    destruct (fvt_of_int_sem_surj (FV := key) n) as (x & Hx & _); first (unfold fvt_of_fv in Hn; lia).
    eq_fvt_of_int_l Hx. eq_fvt_of_int_r Hx.
    eq_pures_l. eq_pures_r.
    iApply (eq_brel_self _ _ _ _ (brel_enc_couple x m)).
    { intros ??. iIntros "(%c & -> & -> & HP)". iExists c. by iFrame. }
    iIntros (vl vr) "(%c & -> & -> & _)". rewrite eq_lift_fvt. iPureIntro. by exists c.
  Qed.

  Lemma enc_real_tape_enc_real :
    ⊢ sem_typed [] (enc_real_tape ske) (enc_real ske) ⊥ (𝟙 ⊸ (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof.
    iApply sem_typed_sub_ty; last iApply (EQ_sem_typed _ _ _ _ enc_real_tape_EQ Fwd).
    iApply (ty_le_mbang_elim MS).
  Qed.

  Lemma enc_real_enc_real_tape :
    ⊢ sem_typed [] (enc_real ske) (enc_real_tape ske) ⊥ (𝟙 ⊸ (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof.
    iApply sem_typed_sub_ty; last iApply (EQ_sem_typed _ _ _ _ enc_real_tape_EQ Bwd).
    iApply (ty_le_mbang_elim MS).
  Qed.

End OTS.

Section rand_fvt_typing.
  Context `{!probblazeRGS Σ} {t : fin_val_type} {s : @fin_val_type_struct t} (fv : @fin_val Σ _ t s).

  Lemma sem_typed_rand_fvt Γ ρ :
    (1 ≤ fin_val_type.card (fin_val_type := t))%nat →
    ⊢ sem_typed Γ (rand_fvt s #()%V) (rand_fvt s #()%V) ρ (sem_τFT (fin_val := fv)) Γ.
  Proof.
    iIntros (Hc γ) "!# HΓ /=". rewrite /rand_fvt. brel_pures_l. brel_pures_r.
    iApply (brel_couple_rand_rand _ _ (λ n : nat, n)).
    { by intros. }
    iIntros (n Hn) "/=".
    destruct (fvt_of_int_sem_surj (FV := fv) n) as (x & Hx & _).
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := fv)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := fv)); first done.
    brel_pures_l. brel_pures_r.
    iModIntro. iFrame. by iExists x.
  Qed.

End rand_fvt_typing.
