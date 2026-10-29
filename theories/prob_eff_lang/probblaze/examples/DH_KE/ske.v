From clutch.prob_eff_lang.probblaze Require Import notation logic sem_judgement sem_types sem_def tactics proofmode.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import fin_val_type.
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

Section OTS.
  Context `{ske : SYM}.

  Lemma enc_real_tape_enc_real : 
    ⊢ sem_typed [] (enc_real_tape ske) (enc_real ske) ⊥ (𝟙 ⊸ (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof.
    iIntros "!# %vs Hvs /=". 
    unfold enc_real_tape, enc_real.
    iApply brel_value. iIntros "$ !>". 
    iSplitL; last done.
    iIntros (??) "(->&->)". 
    brel_pures_l.
    brel_pures_r.
    brel_alloctape_l ι as "Hι".
    iApply (brel_na_alloc (ι ↪N (Z.to_nat (key.(card) - 1); []))%I  (nroot .@ "inv")).
    iSplitL "Hι"; [iNext; iFrame|].
    iIntros "#HI".
    brel_pures_l.
    rewrite /sem_ty_arr /sem_ty_mbang /=.
    iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)". 
    iApply (brel_na_inv _ _ (nroot .@ "inv")); first set_solver.
    iFrame "HI".
    iIntros "(Hι & Hclose)".
    brel_pures_l.
    brel_pures_r.
    rewrite /rand_key /rand_fvt.
    brel_pures_r.
    iApply brel_couple_TU; first done.
    iSplitL "Hι"; first by iApply tapeN_to_empty.
    iIntros (k) "Hι /=".
    iAssert (ι ↪N (Z.to_nat (ks.(card) - 1); [fin_to_nat k]))%I with "[Hι]" as "Hι".
    { iExists [_]. simpl. iFrame. done. }
    brel_rand_l.
    brel_pures_l.
    iApply brel_na_close.
    iFrame "Hclose Hι".
    pose proof (fin_to_nat_lt k) as Hk.
    pose proof kt_nontrivial as Hnt.
    destruct (fvt_of_int_sem_surj (FV := key) (fin_to_nat k)) as (x & Hx & _);
      first (unfold fvt_of_fvts in Hk |- *; lia).
    unshelve iApply (@brel_fvt_of_int_correct_l _ _ kt); try done.
    unshelve iApply (@brel_fvt_of_int_correct_r _ _ kt); try done.
    brel_pures_l.
    brel_pures_r.
    unfold fvtval_as.
    iApply brel_wand; first iApply (brel_enc_couple x m).
    iIntros "!>" (??) "(%&H1&H2&_)".
    iExists c.
    unfold fvtval_as. 
    iFrame.
  Qed.

  Lemma enc_real_enc_real_tape : 
    ⊢ sem_typed [] (enc_real ske) (enc_real_tape ske) ⊥ (𝟙 ⊸ (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof.
    iIntros "!# %vs Hvs /=".
    unfold enc_real_tape, enc_real.
    iApply brel_value. iIntros "$ !>". 
    iSplitL; last done.
    iIntros (??) "(->&->)". 
    brel_pures_l.
    brel_pures_r.
    brel_alloctape_r ι as "Hι".
    iApply (brel_na_alloc (ι ↪ₛ (Z.to_nat (ks.(card) - 1); []))%I (nroot .@ "inv")).
    iSplitL "Hι"; [iNext; iFrame|].
    iIntros "#HI".
    brel_pures_r.
    rewrite /sem_ty_arr /sem_ty_mbang /=.
    iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    iApply (brel_na_inv _ _ (nroot .@ "inv")); first set_solver.
    iFrame "HI".
    iIntros "(Hι & Hclose)".
    brel_pures_l.
    brel_pures_r.
    rewrite /rand_key /rand_fvt.
    brel_pures_l.
    iApply brel_couple_UT; first done.
    iSplitL "Hι"; first by iApply empty_to_spec_tapeN.
    iIntros (k Hlt) "!> Hι /=".
    brel_rand_r.
    brel_pures_r.
    iApply brel_na_close.
    iFrame "Hclose".
    iSplitL "Hι"; first (iNext; by iApply spec_tapeN_to_empty).
    pose proof kt_nontrivial as Hnt.
    destruct (fvt_of_int_sem_surj (FV := key) k) as (x & Hx & _);
      first (unfold fvt_of_fvts in Hlt |- *; lia).
    unshelve iApply (@brel_fvt_of_int_correct_l _ _ kt); try done.
    unshelve iApply (@brel_fvt_of_int_correct_r _ _ kt); try done.
    brel_pures_l.
    brel_pures_r.
    unfold fvtval_as.
    iApply brel_wand; first iApply (brel_enc_couple x m).
    iIntros "!>" (??) "(%&H1&H2&_)".
    iExists c.
    unfold fvtval_as. 
    iFrame.
  Qed. 


End OTS.


