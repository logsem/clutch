From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import notation logic sem_judgement sem_types sem_def tactics proofmode adequacy.
From clutch.prob_eff_lang.probblaze Require compatibility sem_operators sem_row sem_env sem_sig.
From clutch.prob_eff_lang.probblaze.examples Require Import fin_val_type fin_val_type_prod ske.
Set Default Proof Using "Type*".

(* PRP function F that is assumed to be PRF secure as in Joy of Cryptography [Mike Rosulek] *)

(** A symmetric encryption scheme built from an abstract keyed function
    [prf : key → nonce → message]: [enc k m = (r, prf k r + m mod |M|)] for a
    fresh nonce [r].  The ciphertext space is the product [fin_val] of nonces and
    messages ([fin_val_type_prod]). *)

Class PRF_struct {kt nt mt : fin_val_type}
  {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt} :=
  { prf : val
  ; prf_closed : is_closed_val prf }.

#[export] Hint Resolve prf_closed : core.

(** Determinism of [prf]: it computes the Coq function [prf_sem]. *)
Class PRF `{HΣ : probblazeRGS Σ} {kt nt mt : fin_val_type}
  {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}
  {key : @fin_val Σ HΣ _ ks} {nonce : @fin_val Σ HΣ _ ns} {msg : @fin_val Σ HΣ _ ms}
  {prf_struct : @PRF_struct kt nt mt ks ns ms} :=
  { prf_sem : kt → nt → mt
  ; brel_prf_l : ∀ (k : kt) (x : nt) K e E X R,
      BREL fill K (fvtval (prf_sem k x)) ≤ e @ E <|X|> {{ R }} -∗
      BREL fill K (prf (fvtval k) (fvtval x)) ≤ e @ E <|X|> {{ R }}
  ; brel_prf_r : ∀ (k : kt) (x : nt) K e E X R,
      BREL e ≤ fill K (fvtval (prf_sem k x)) @ E <|X|> {{ R }} -∗
      BREL e ≤ fill K (prf (fvtval k) (fvtval x)) @ E <|X|> {{ R }}
  }.

(** * The PRF games - Joy of Cryptography def. 6.1.1 *)
Section prf_games.
  Context {kt nt mt : fin_val_type}.
  Context {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {prf_struct : @PRF_struct kt nt mt ks ns ms}.

  Definition rand_prf_key : val := rand_fvt ks.
  Definition rand_prf_out : val := rand_fvt ms.

  (** Each call of the outer function draws a fresh key / a fresh random function. *)
  Definition prf_real : val :=
    λ: <>, let: "k" := rand_prf_key #()%V in λ: "x", prf "k" "x".

  (** A lazily sampled random function, its table kept as a closure. *)
  Definition prf_ideal : val :=
    λ: <>,
      let: "tbl" := ref (λ: <>, NONE) in
      λ: "x",
        let: "i" := ns.(int_of_fvt) "x" in
        match: (!"tbl") "i" with
          NONE =>
            let: "y" := rand_prf_out #()%V in
            let: "old" := !"tbl" in
            "tbl" <- (λ: "j", if: "j" = "i" then SOME "y" else "old" "j") ;;
            "y"
        | SOME "y" => "y"
        end.

  Context {nonce : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ nt ns}.
  Context {msg : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ mt ms}.

  Definition τprf `{!probblazeRGS Σ} : sem_ty Σ :=
    (𝟙 → (sem_τFT (fin_val := nonce Σ _) → sem_τFT (fin_val := msg Σ _)))%T.

  Definition prf_adversary (A : val) : Prop :=
    ∀ `{!probblazeRGS Σ}, ⊢ ⊨ᵥ A ≤ A : (τprf → 𝔹).

End prf_games.

(** * The scheme - Joy of Cryptography construction 8.3.1 *)
Section scheme.
  Context {kt nt mt : fin_val_type}.
  Context {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {prf_struct : @PRF_struct kt nt mt ks ns ms}.
  Context `{!Inhabited (fvt_sort ks), !Inhabited (fvt_sort ns), !Inhabited (fvt_sort ms)}.

  #[local] Notation N := (fin_val_type.card (fin_val_type := mt)).
  #[local] Notation CT := (@prod_fvt nt mt).
  #[local] Notation CS := (@prod_fvts nt mt ns ms).

  #[local] Instance prod_fvt_inhabited : Inhabited (fvt_sort CS) := populate (inhabitant, inhabitant).

  Definition rand_nonce : val := rand_fvt ns.

  Definition enc_prf : val :=
    λ: "k" "m",
      let: "r" := rand_nonce #()%V in
      let: "p" := (ms.(int_of_fvt) (prf "k" "r") + ms.(int_of_fvt) "m") `rem` #N in
      match: ms.(fvt_of_int) "p" with
        NONE => #()%V
      | SOME "c" => ("r", "c")
      end.

  Definition dec_prf : val :=
    λ: "k" "c",
      ms.(fvt_of_int) ((ms.(int_of_fvt) (Snd "c") - ms.(int_of_fvt) (prf "k" (Fst "c")) + #N) `rem` #N).

  Lemma enc_prf_closed : is_closed_val enc_prf.
  Proof. is_closed. Qed.
  Lemma dec_prf_closed : is_closed_val dec_prf.
  Proof. is_closed. Qed.

  Global Instance prf_sym_struct : @SYM_struct kt ks mt ms CT CS :=
    { enc := enc_prf
    ; dec := dec_prf
    ; enc_closed := enc_prf_closed
    ; dec_closed := dec_prf_closed }.

  (** The tail of [enc_prf]: pad [y] with [m] and pair it with the nonce [r]. *)
  Definition pad_enc : val :=
    λ: "r" "y" "m",
      let: "p" := (ms.(int_of_fvt) "y" + ms.(int_of_fvt) "m") `rem` #N in
      match: ms.(fvt_of_int) "p" with
        NONE => #()%V
      | SOME "c" => ("r", "c")
      end.

  (** The reduction: [enc_prf] with [prf "k"] replaced by an oracle from the PRF game
      [F].  One fresh oracle per message, as [enc_real] draws one key per message. *)
  Definition red_prf : val :=
    λ: "F" <> "m",
      let: "f" := "F" #()%V in
      let: "r" := rand_nonce #()%V in
      pad_enc "r" ("f" "r") "m".

  (** Hybrid between [red_prf prf_ideal] and [enc_ideal]: nonce and pad drawn as raw
      integers from tapes, and the message ignored.  The pair is decoded from its code,
      as [rand_cipher] does. *)
  Definition enc_hyb : val :=
    λ: <>,
      let: "ιr" := alloc #(ns.(card) - 1) in
      let: "ιp" := alloc #(ms.(card) - 1) in
      λ: "m",
        let: "r" := rand("ιr") #(Z.to_nat (ns.(card) - 1)) in
        let: "p" := rand("ιp") #(Z.to_nat (ms.(card) - 1)) in
        match: CS.(fvt_of_int) ("r" * #N + "p") with
          NONE => #()%V
        | SOME "c" => "c"
        end.

End scheme.

Lemma pad_code_Z (y m N : nat) : (0 < N)%nat →
  ((Z.of_nat y + Z.of_nat m) `rem` Z.of_nat N)%Z = Z.of_nat ((y + m) `mod` N).
Proof. intros. rewrite Nat2Z.inj_mod Z.rem_mod_nonneg; lia. Qed.

Lemma unpad_code_Z (y m N : nat) : (y < N)%nat → (m < N)%nat →
  ((Z.of_nat ((y + m) `mod` N) - Z.of_nat y + Z.of_nat N) `rem` Z.of_nat N)%Z = Z.of_nat m.
Proof.
  intros Hy Hm. rewrite Z.rem_mod_nonneg; [|lia|lia].
  destruct (Nat.lt_ge_cases (y + m) N) as [Hlt|Hge].
  - rewrite Nat.mod_small //.
    replace ((y + m)%nat - y + N)%Z with (Z.of_nat m + 1 * Z.of_nat N)%Z by lia.
    rewrite Z.mod_add; [|lia]. rewrite Z.mod_small; lia.
  - assert ((y + m) `mod` N = y + m - N)%nat as ->.
    { rewrite (Nat.Div0.mod_eq (y + m) N).
      assert ((y + m) `div` N = 1)%nat as ->.
      { symmetry. apply Nat.div_unique with (y + m - N)%nat; lia. }
      lia. }
    rewrite Z.mod_small; lia.
Qed.

Lemma code_pair_inj (n1 n2 n1' n2' N : nat) :
  (n2 < N)%nat → (n2' < N)%nat → (n1 * N + n2 = n1' * N + n2')%nat → n1 = n1' ∧ n2 = n2'.
Proof.
  intros. assert (n1 = n1') by (destruct (Nat.lt_total n1 n1') as [?|[?|?]]; nia).
  split; [done|lia].
Qed.

(** The one-time pad [y ↦ (y + k) mod N] on [y < N], extended by the identity. *)
Definition pad_map (N k y : nat) : nat :=
  if bool_decide (y < N)%nat then
    (if bool_decide (y + k mod N < N)%nat then y + k mod N else y + k mod N - N)%nat
  else y.

#[local] Instance pad_map_bij N k : Bij (pad_map N k).
Proof.
  rewrite /pad_map.
  destruct (decide (N = 0)%nat) as [->|HN].
  { split; [intros ??; repeat case_bool_decide; lia|intros y; by exists y; repeat case_bool_decide; lia]. }
  pose proof (Nat.mod_upper_bound k N HN).
  split.
  - intros y y'. repeat case_bool_decide; lia.
  - intros z. destruct (decide (z < N)%nat).
    + destruct (decide (k mod N ≤ z)%nat).
      * exists (z - k mod N)%nat. repeat case_bool_decide; lia.
      * exists (z + N - k mod N)%nat. repeat case_bool_decide; lia.
    + exists z. repeat case_bool_decide; lia.
Qed.

Lemma pad_map_mod N k y : (y < N)%nat → pad_map N k y = ((y + k) `mod` N)%nat.
Proof.
  intros Hy. rewrite /pad_map. pose proof (Nat.mod_upper_bound k N ltac:(lia)).
  rewrite (Nat.Div0.add_mod y k N) (Nat.mod_small y N) //.
  repeat case_bool_decide; try lia.
  - by rewrite (Nat.mod_small (y + k mod N)).
  - symmetry. rewrite (Nat.Div0.mod_eq (y + k mod N) N).
    assert ((y + k `mod` N) `div` N = 1)%nat as ->.
    { symmetry. apply Nat.div_unique with (y + k mod N - N)%nat; lia. }
    lia.
Qed.

Lemma pad_map_lt N k y : (y < N)%nat → (pad_map N k y < N)%nat.
Proof. intros. rewrite /pad_map. pose proof (Nat.mod_upper_bound k N ltac:(lia)). repeat case_bool_decide; lia. Qed.

Lemma pad_map_inv N k p : (p < N)%nat → ((pad_map N (N - k mod N) p + k) `mod` N)%nat = p.
Proof.
  intros Hp. rewrite pad_map_mod // Nat.Div0.add_mod_idemp_l.
  pose proof (Nat.mod_upper_bound k N ltac:(lia)).
  rewrite {2}(Nat.Div0.div_mod k N).
  replace (p + (N - k `mod` N) + (N * (k `div` N) + k `mod` N))%nat
    with (p + (1 + k `div` N) * N)%nat by lia.
  rewrite Nat.Div0.mod_add Nat.mod_small //.
Qed.

Section scheme_spec.
  Context `{probblazeRGS Σ}.
  Context {kt nt mt : fin_val_type}.
  Context {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {key : @fin_val Σ _ _ ks} {nonce : @fin_val Σ _ _ ns} {msg : @fin_val Σ _ _ ms}.
  Context {prf_struct : @PRF_struct kt nt mt ks ns ms}.
  Context {PRF_inst : @PRF Σ _ kt nt mt ks ns ms key nonce msg prf_struct}.
  Context `{!Inhabited (fvt_sort ks), !Inhabited (fvt_sort ns), !Inhabited (fvt_sort ms)}.

  Hypothesis kt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := kt))%nat.
  Hypothesis nt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := nt))%nat.
  Hypothesis mt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := mt))%nat.

  #[local] Notation N := (fin_val_type.card (fin_val_type := mt)).
  #[local] Notation CT := (@prod_fvt nt mt).
  #[local] Notation CS := (@prod_fvts nt mt ns ms).
  #[local] Notation CIPHER := (@prod_fv Σ _ nt mt ns ms nonce msg).
  #[local] Notation nonce_rand := (@rand_nonce nt ns).
  #[local] Notation ENC := (@enc_prf kt nt mt ks ns ms prf_struct).
  #[local] Notation DEC := (@dec_prf kt nt mt ks ns ms prf_struct).

  (** The pad of [m] under nonce [r]. *)
  Definition pad_sem (k : kt) (r : nt) (m : mt) : nat :=
    ((int_of_fvt_sem (fin_val := msg) (prf_sem k r) + int_of_fvt_sem (fin_val := msg) m) `mod` N)%nat.

  Lemma rand_nonce_coupl E K K' X R :
    (∀ r : nt, BREL fill K (fvtval r) ≤ fill K' (fvtval r) @ E <|X|> {{R}}) -∗
    BREL fill K (nonce_rand #()%V) ≤ fill K' (nonce_rand #()%V) @ E <|X|> {{R}}.
  Proof.
    iIntros "Hkont". rewrite /rand_nonce /rand_fvt /=.
    brel_pures_l. brel_pures_r.
    iApply (brel_couple_rand_rand _ _ (λ n : nat, n)).
    { by intros. }
    iIntros (c) "%Hlt". rewrite !fill_app /=.
    apply Nat.lt_succ_r in Hlt. unfold fvt_of_fvts in Hlt.
    destruct (fvt_of_int_sem_surj (FV := nonce) c) as (x & Hx & _); first lia.
    iApply (brel_fvt_of_int_correct_l (fin_val := nonce)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := nonce)); first done.
    rewrite !fill_app /=. brel_pures_l. brel_pures_r.
    by iApply "Hkont".
  Qed.

  Lemma prf_brel_enc_couple (k : kt) (m : mt) :
    ⊢ BREL (ENC (fvtval k) (fvtval m)) ≤ ENC (fvtval k) (fvtval m) <|⊥|>
        {{ (λ v1 v2, ∃ c : CT, ⌜v1 = fvtval c⌝ ∗ ⌜v2 = fvtval c⌝ ∗
             ⌜int_of_fvt_sem (fin_val := msg) c.2 = pad_sem k c.1 m⌝) }}.
  Proof.
    rewrite /enc_prf. brel_pures_l. brel_pures_r.
    iApply (rand_nonce_coupl _ [AppRCtx _] [AppRCtx _]). iIntros (r) "/=".
    brel_pures_l. brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    iApply (brel_prf_l (PRF := PRF_inst)). iApply (brel_prf_r (PRF := PRF_inst)).
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    brel_pures_l. brel_pures_r.
    rewrite pad_code_Z; [|lia].
    destruct (fvt_of_int_sem_surj (FV := msg) (pad_sem k r m)) as (c & Hc & Hcc).
    { apply Nat.mod_upper_bound. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first done.
    brel_pures_l. brel_pures_r.
    iModIntro. iExists (r, c). by do 2 (iSplit; [done|]).
  Qed.

  Lemma prf_dec_correct_l (k : kt) (m : mt) (c : CT) K e E X R :
    ⌜int_of_fvt_sem (fin_val := msg) c.2 = pad_sem k c.1 m⌝ -∗
    BREL fill K (SOMEV (fvtval m)) ≤ e @ E <|X|> {{ R }} -∗
    BREL fill K (DEC (fvtval k) (fvtval (fin_val_type := CT) c)) ≤ e @ E <|X|> {{ R }}.
  Proof.
    destruct c as [r p]. iIntros "%Hp H". rewrite /dec_prf /=. brel_pures_l.
    iApply (brel_prf_l (PRF := PRF_inst)). rewrite fill_app /=.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)). rewrite fill_app /=.
    brel_pures_l.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)). rewrite fill_app /=.
    brel_pures_l.
    rewrite Hp /pad_sem unpad_code_Z; try apply (int_of_fvt_sem_bound (fin_val := msg)).
    by iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first apply int_of_fvt_of_int_sem.
  Qed.

  Lemma prf_dec_correct_r (k : kt) (m : mt) (c : CT) K e E X R :
    ⌜int_of_fvt_sem (fin_val := msg) c.2 = pad_sem k c.1 m⌝ -∗
    BREL e ≤ fill K (SOMEV (fvtval m)) @ E <|X|> {{ R }} -∗
    BREL e ≤ fill K (DEC (fvtval k) (fvtval (fin_val_type := CT) c)) @ E <|X|> {{ R }}.
  Proof.
    destruct c as [r p]. iIntros "%Hp H". rewrite /dec_prf /=. brel_pures_r.
    iApply (brel_prf_r (PRF := PRF_inst)). rewrite fill_app /=.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)). rewrite fill_app /=.
    brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)). rewrite fill_app /=.
    brel_pures_r.
    rewrite Hp /pad_sem unpad_code_Z; try apply (int_of_fvt_sem_bound (fin_val := msg)).
    by iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first apply int_of_fvt_of_int_sem.
  Qed.

  Lemma prf_dec_typed :
    ⊢ ⊨ᵥ DEC ≤ DEC : (key.(sem_τFT) -{ ⊥ }-> CIPHER.(sem_τFT) -{ ⊥ }-> Option msg.(sem_τFT)).
  Proof.
    rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!# !#" (k1 k2) "(%k & -> & ->)".
    rewrite /dec_prf. brel_pures_l. brel_pures_r.
    iIntros "!> !#" (c1 c2) "(%c & -> & ->)". destruct c as [r p]. simpl.
    brel_pures_l. brel_pures_r.
    iApply (brel_prf_l (PRF := PRF_inst)). iApply (brel_prf_r (PRF := PRF_inst)).
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    brel_pures_l. brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    brel_pures_l. brel_pures_r.
    set (a := int_of_fvt_sem (fin_val := msg) p).
    set (y := int_of_fvt_sem (fin_val := msg) (prf_sem k r)).
    assert (Hy : (y < N)%nat) by apply (int_of_fvt_sem_bound (fin_val := msg)).
    assert (((Z.of_nat a - Z.of_nat y + Z.of_nat N) `rem` Z.of_nat N)%Z
            = Z.of_nat ((a + N - y) `mod` N)) as ->.
    { rewrite Z.rem_mod_nonneg; [|lia|lia]. rewrite Nat2Z.inj_mod. f_equal. lia. }
    destruct (fvt_of_int_sem (fin_val := msg) ((a + N - y) `mod` N)) as [m|] eqn:Hm.
    - iApply (brel_fvt_of_int_correct_l (fin_val := msg) _ []); first done.
      iApply (brel_fvt_of_int_correct_r (fin_val := msg) _ []); first done.
      iApply brel_value. iIntros "$ !>". iExists _, _. iRight.
      do 2 (iSplit; [done|]). by iExists m.
    - iApply (brel_fvt_of_int_none_l (fin_val := msg) _ []); first done.
      iApply (brel_fvt_of_int_none_r (fin_val := msg) _ []); first done.
      iApply brel_value. iIntros "$ !>". iExists _, _. by iLeft.
  Qed.

  Program Global Instance PRF_SKE :
    @SYM Σ _ kt mt CT ks ms CS key msg CIPHER
         (@prf_sym_struct kt nt mt ks ns ms prf_struct _ _ _) :=
    { P k m c := ⌜int_of_fvt_sem (fin_val := msg) c.2 = pad_sem k c.1 m⌝%I
    ; brel_enc_couple := prf_brel_enc_couple
    ; brel_dec_enc_correct_l := prf_dec_correct_l
    ; brel_dec_enc_correct_r := prf_dec_correct_r
    ; dec_typed := prf_dec_typed }.
  Next Obligation. exact kt_nontriv. Qed.
  Next Obligation. rewrite /fvt_of_fvts prod_fvt_card. nia. Qed.

End scheme_spec.


(** * Reduction of [enc_real]/[enc_ideal] to [prf_real]/[prf_ideal]

    [enc_real ≃ red_prf prf_real]              (pure bookkeeping)
    [red_prf prf_real ≈ red_prf prf_ideal]     (the PRF advantage)
    [red_prf prf_ideal ≃ enc_hyb]              (table fresh; pad is a one-time pad)
    [enc_hyb ≃ enc_ideal]                      (two tape samples coupled with one) *)
Section reduction_spec.
  Context `{probblazeRGS Σ}.
  Context {kt nt mt : fin_val_type}.
  Context {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {key : @fin_val Σ _ _ ks} {nonce : @fin_val Σ _ _ ns} {msg : @fin_val Σ _ _ ms}.
  Context {prf_struct : @PRF_struct kt nt mt ks ns ms}.
  Context {PRF_inst : @PRF Σ _ kt nt mt ks ns ms key nonce msg prf_struct}.
  Context `{!Inhabited (fvt_sort ks), !Inhabited (fvt_sort ns), !Inhabited (fvt_sort ms)}.

  Hypothesis kt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := kt))%nat.
  Hypothesis nt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := nt))%nat.
  Hypothesis mt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := mt))%nat.

  #[local] Notation CS := (@prod_fvts nt mt ns ms).
  #[local] Notation CIPHER := (@prod_fv Σ _ nt mt ns ms nonce msg).
  #[local] Notation SKES := (@prf_sym_struct kt nt mt ks ns ms prf_struct _ _ _).
  #[local] Notation RED := (@red_prf nt mt ns ms).
  #[local] Notation HYB := (@enc_hyb nt mt ns ms).
  #[local] Notation PREAL := (@prf_real kt nt mt ks ns ms prf_struct).
  #[local] Notation PIDEAL := (@prf_ideal nt mt ns ms).
  #[local] Notation PAD := (@pad_enc mt ms).

  #[local] Notation N := (fin_val_type.card (fin_val_type := mt)).
  #[local] Notation Key := (sem_τFT (fin_val := key)).
  #[local] Notation Nonce := (sem_τFT (fin_val := nonce)).
  #[local] Notation Msg := (sem_τFT (fin_val := msg)).
  #[local] Notation Cph := (sem_τFT (fin_val := CIPHER)).
  #[local] Notation τP := (𝟙 → (Nonce → Msg))%T.
  #[local] Notation τE := (𝟙 ⊸ (Msg → Cph))%T.

  (** ** Typing, for [advantage_reduction_expr] *)
  Section typing.
    Import compatibility sem_row sem_env sem_sig typed_hint_modes.
    #[local] Existing Instance multi_ty_fvt.
    #[local] Notation N := (fin_val_type.card (fin_val_type := mt)).

    Lemma sem_typed_prf Γ1 Γ2 Γ3 e1 e1' e2 e2' ρ :
      ⊢ sem_typed Γ1 e2 e2' ρ Nonce Γ2 -∗ sem_typed Γ2 e1 e1' ρ Key Γ3 -∗
        sem_typed Γ1 (prf e1 e2) (prf e1' e2') ρ Msg Γ3.
    Proof.
      iIntros "#He2 #He1 !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
      iIntros "!# % % ((%x & -> & ->) & HΓ2) /=".
      iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]);
        [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ2]"); first by iApply "He1".
      iIntros "!# % % ((%k & -> & ->) & HΓ3) /=".
      iApply (brel_prf_l (PRF := PRF_inst) _ _ []). iApply (brel_prf_r (PRF := PRF_inst) _ _ []).
      iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
    Qed.

    Lemma pad_enc_typed : ⊢ ⊨ᵥ PAD ≤ PAD : (Nonce → (Msg → (Msg → Cph))).
    Proof.
      rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /sem_ty_arr /=.
      iIntros "!# !#" (r1 r2) "(%r & -> & ->)".
      rewrite /pad_enc. brel_pures_l. brel_pures_r.
      iIntros "!> !#" (y1 y2) "(%y & -> & ->)".
      brel_pures_l. brel_pures_r.
      iIntros "!> !#" (m1 m2) "(%m & -> & ->)".
      brel_pures_l. brel_pures_r.
      iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
      iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
      iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
      iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
      brel_pures_l. brel_pures_r.
      rewrite pad_code_Z; last lia.
      destruct (fvt_of_int_sem_surj (FV := msg)
                  ((int_of_fvt_sem (fin_val := msg) y + int_of_fvt_sem (fin_val := msg) m) `mod` N))
        as (c & Hc & _).
      { apply Nat.mod_upper_bound. lia. }
      iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first done.
      iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first done.
      brel_pures_l. brel_pures_r.
      iModIntro. by iExists (r, c).
    Qed.

    Lemma red_prf_typed : ⊢ ⊨ᵥ RED ≤ RED : (τP → τE).
    Proof.
      iApply sem_typed_closure; first done. simpl.
      iApply (sem_typed_oval _ [_] []). iApplyT sem_oval_typed_afun. simpl.
      iApply (sem_typed_oval _ [_] []). iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_let.
      { iApplyT (sem_typed_app_gen 𝟙 ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |iApply sem_typed_unit].
        typed_cont. }
      rewrite /rand_nonce.
      iApplyT sem_typed_let; first iApply (sem_typed_rand_fvt nonce); first done.
      (* [PAD "r" ("f" "r") "m"] *)
      iApplyT (sem_typed_app_gen Msg ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |typed_var].
      iApplyT sem_typed_sub_ty; first iApply ty_le_mbang_elim.
      iApplyT (sem_typed_app_gen Msg ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |].
      2: { iApplyT (sem_typed_app_gen Nonce ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |typed_var_copy].
           typed_cont. }
      iApplyT sem_typed_sub_ty; first iApply ty_le_mbang_elim.
      iApplyT (sem_typed_app_gen Nonce ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |typed_var].
      iApplyT sem_typed_sub_ty; first iApply ty_le_mbang_elim.
      simpl. iApply sem_typed_sub_nil. iApply sem_typed_val. iApply pad_enc_typed.
      Unshelve. all: try solve_typed_side.
    Qed.

    Lemma prf_real_typed : ⊢ ⊨ᵥ PREAL ≤ PREAL : τP.
    Proof.
      iApply sem_typed_closure; first done. simpl. rewrite /rand_prf_key.
      iApplyT sem_typed_let; first iApply (sem_typed_rand_fvt key); first done.
      iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_prf; typed_var.
      Unshelve. all: try solve_typed_side.
    Qed.

    (** The table is a copyable reference to a function [ℤ → Option Msg]. *)
    Lemma prf_ideal_typed : ⊢ ⊨ᵥ PIDEAL ≤ PIDEAL : τP.
    Proof.
      iApply sem_typed_closure; first done. simpl.
      iApplyT sem_typed_let.
      { iApply (sem_typed_alloc_cpy (ℤ → Option Msg)%T).
        iApply (sem_typed_oval _ [] []). iApplyT sem_oval_typed_ufun. simpl.
        iApply sem_typed_injl. iApply sem_typed_unit. }
      iApply (sem_typed_oval _ [_] []). iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_let; first (iApply (sem_typed_int_of_fvt nonce); typed_var).
      iApplyT (sem_typed_match_split [] []).
      - (* lookup *)
        iApplyT (sem_typed_app_gen ℤ ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |typed_var_copy].
        iApplyT sem_typed_sub_ty; first iApply ty_le_mbang_elim.
        iApplyT sem_typed_load_cpy. typed_var_copy.
      - iApply env_le_refl.
      - (* miss: sample, extend the table *)
        simpl. rewrite /rand_prf_out.
        iApplyT sem_typed_let; first (iApply (sem_typed_rand_fvt msg); lia).
        iApplyT sem_typed_let; first (iApplyT sem_typed_load_cpy; typed_var_copy).
        iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
        iApplyT sem_typed_seq.
        + iApplyT (sem_typed_store_cpy_gen (ℤ → Option Msg)%T); last first.
          { iApplyT (sem_typed_sub_env _ ([("old", _); ("y", _); ("i", _)] ++ [("y", _); ("tbl", _)]));
              first env_solve.
            iApply (sem_typed_oval _ [_; _; _] [_; _]). iApplyT sem_oval_typed_ufun. simpl.
            iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
            iApplyT sem_typed_if.
            * iApply (sem_typed_bin_op EqOp ℤ ℤ 𝔹); [apply sem_operators.typed_bin_op_Eq| |typed_var].
              typed_var_copy.
            * iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
              iApply sem_typed_injr. typed_var.
            * iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
              iApplyT (sem_typed_app_gen ℤ ⟨⟩%R ⟨⟩%R ⟨⟩%R); [iApply row_le_refl|iApply row_le_refl| |typed_var].
              typed_cont. }
          typed_var.
        + typed_var.
      - iApply env_le_nil.
      - iApply env_le_refl.
      - (* hit *)
        iApplyT sem_typed_sub_env_final; first iApply env_le_nil. typed_var.
      - iApply env_le_nil.
      Unshelve. all: try solve_typed_side.
    Qed.

  End typing.

  (** ** The refinements *)

  (* Lockstep: both sides draw the key, then the nonce, then evaluate [prf k r]. *)
  Lemma enc_real_red_real : ⊢ sem_typed [] (enc_real SKES) (RED PREAL) ⊥ τE [].
  Proof.
    iIntros "!# %vs Hvs /=". rewrite /red_prf /pad_enc /enc_real.
    brel_pures_r. iModIntro. iSplitR "Hvs"; last done.
    iIntros (??) "(->&->)".
    brel_pures_l. brel_pures_r. rewrite /sem_ty_arr /sem_ty_mbang /=. iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    brel_pures_l. brel_pures_r.
    rewrite /prf_real /rand_key /rand_prf_key /rand_fvt /=. brel_pures_l. brel_pures_r.
    iApply (brel_couple_rand_rand _ _ (λ n : nat, n)).
    { by intros. }
    iIntros (k Hk) "/=".
    destruct (fvt_of_int_sem_surj (FV := key) k) as (kv & Hkv & _).
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := key)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := key)); first done.
    rewrite /enc_prf. brel_pures_l. brel_pures_r.
    rewrite /rand_nonce /rand_fvt. brel_pures_l. brel_pures_r.
    iApply (brel_couple_rand_rand _ _ (λ n : nat, n)).
    { by intros. }
    iIntros (r Hr) "/=".
    destruct (fvt_of_int_sem_surj (FV := nonce) r) as (rv & Hrv & Hrv').
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := nonce)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := nonce)); first done.
    brel_pures_l. brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_prf_l (PRF := PRF_inst)). iApply (brel_prf_r (PRF := PRF_inst)).
    brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    brel_pures_l. brel_pures_r.
    rewrite pad_code_Z; last lia.
    destruct (fvt_of_int_sem_surj (FV := msg)
                ((int_of_fvt_sem (fin_val := msg) (prf_sem kv rv) + int_of_fvt_sem (fin_val := msg) m) `mod` N))
      as (c & Hc & _).
    { apply Nat.mod_upper_bound. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first done.
    brel_pures_l. brel_pures_r.
    iModIntro. by iExists (rv, c).
  Qed.

  Lemma red_real_enc_real : ⊢ sem_typed [] (RED PREAL) (enc_real SKES) ⊥ τE [].
  Proof.
    iIntros "!# %vs Hvs /=". rewrite /red_prf /pad_enc /enc_real.
    brel_pures_l. iModIntro. iSplitR "Hvs"; last done.
    iIntros (??) "(->&->)".
    brel_pures_l. brel_pures_r. rewrite /sem_ty_arr /sem_ty_mbang /=. iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    brel_pures_l. brel_pures_r.
    rewrite /prf_real /rand_key /rand_prf_key /rand_fvt /=. brel_pures_l. brel_pures_r.
    iApply (brel_couple_rand_rand _ _ (λ n : nat, n)).
    { by intros. }
    iIntros (k Hk) "/=".
    destruct (fvt_of_int_sem_surj (FV := key) k) as (kv & Hkv & _).
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := key)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := key)); first done.
    rewrite /enc_prf. brel_pures_l. brel_pures_r.
    rewrite /rand_nonce /rand_fvt. brel_pures_l. brel_pures_r.
    iApply (brel_couple_rand_rand _ _ (λ n : nat, n)).
    { by intros. }
    iIntros (r Hr) "/=".
    destruct (fvt_of_int_sem_surj (FV := nonce) r) as (rv & Hrv & Hrv').
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := nonce)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := nonce)); first done.
    brel_pures_l. brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    iApply (brel_prf_l (PRF := PRF_inst)). iApply (brel_prf_r (PRF := PRF_inst)).
    brel_pures_l.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    brel_pures_l. brel_pures_r.
    rewrite pad_code_Z; last lia.
    destruct (fvt_of_int_sem_surj (FV := msg)
                ((int_of_fvt_sem (fin_val := msg) (prf_sem kv rv) + int_of_fvt_sem (fin_val := msg) m) `mod` N))
      as (c & Hc & _).
    { apply Nat.mod_upper_bound. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first done.
    brel_pures_l. brel_pures_r.
    iModIntro. by iExists (rv, c).
  Qed.

  Lemma red_ideal_hyb : ⊢ sem_typed [] (RED PIDEAL) HYB ⊥ τE [].
  Proof.
    iIntros "!# %vs Hvs /=". rewrite /red_prf /pad_enc /enc_hyb.
    brel_pures_l. iModIntro. iSplitR "Hvs"; last done.
    iIntros (??) "(->&->)".
    brel_pures_l. brel_pures_r.
    brel_alloctape_r ιr as "Hιr". brel_pures_r.
    brel_alloctape_r ιp as "Hιp".
    iApply (brel_na_alloc (ιr ↪ₛ (Z.to_nat (ns.(card) - 1); [])
                           ∗ ιp ↪ₛ (Z.to_nat (ms.(card) - 1); []))%I (nroot .@ "hyb")).
    iSplitL "Hιr Hιp"; [iNext; iFrame|]. iIntros "#HI".
    brel_pures_r. rewrite /sem_ty_arr /sem_ty_mbang /=. iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    iApply (brel_na_inv _ _ (nroot .@ "hyb")); first set_solver.
    iFrame "HI". iIntros "((Hιr & Hιp) & Hclose)".
    brel_pures_l. brel_pures_r.
    (* the fresh table of [prf_ideal] *)
    rewrite /prf_ideal. brel_pures_l.
    brel_alloc_l ℓ as "Hℓ". brel_pures_l.
    (* the nonce, presampled on the right *)
    rewrite /rand_nonce /rand_fvt. brel_pures_l.
    iApply (brel_couple_UT _ _ (λ n : nat, n)).
    { by intros. }
    iSplitL "Hιr"; first (iNext; by iApply empty_to_spec_tapeN).
    iIntros "!>" (r Hr) "Hιr /=".
    destruct (fvt_of_int_sem_surj (FV := nonce) r) as (rv & Hrv & Hrv').
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := nonce)); first done.
    brel_pures_l.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := nonce)). brel_pures_l.
    (* the table misses; the oracle output becomes the pad on the right *)
    brel_load_l. brel_pures_l.
    rewrite /rand_prf_out /rand_fvt. brel_pures_l.
    iApply (brel_couple_UT _ _ (pad_map N (int_of_fvt_sem (fin_val := msg) m))).
    { intros. unfold fvt_of_fvts in *; simpl in *.
      assert (S (Z.to_nat (N - 1)) = N) as -> by lia. apply pad_map_lt. lia. }
    iSplitL "Hιp"; first (iNext; by iApply empty_to_spec_tapeN).
    iIntros "!>" (y Hy) "Hιp /=".
    destruct (fvt_of_int_sem_surj (FV := msg) y) as (yv & Hyv & Hyv').
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first done.
    brel_pures_l. brel_load_l. brel_pures_l. brel_store_l. brel_pures_l.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := msg)). brel_pures_l.
    brel_rand_r. brel_pures_r. brel_rand_r. brel_pures_r.
    iApply brel_na_close. iFrame "Hclose".
    iSplitL "Hιr Hιp"; first (iNext; iSplitL "Hιr"; by iApply spec_tapeN_to_empty).
    unfold fvt_of_fvts in *. simpl in *.
    assert (y < N)%nat as HyN by lia.
    rewrite Hyv' pad_code_Z; last lia.
    rewrite pad_map_mod //.
    pose proof (Nat.mod_upper_bound (y + int_of_fvt_sem (fin_val := msg) m) N ltac:(lia)).
    destruct (fvt_of_int_sem_surj (FV := msg) ((y + int_of_fvt_sem (fin_val := msg) m) `mod` N))
      as (c & Hc & Hc'); first lia.
    iApply (brel_fvt_of_int_correct_l (fin_val := msg)); first done.
    brel_pures_l.
    rewrite -Hrv' -Hc' -Nat2Z.inj_mul -Nat2Z.inj_add.
    iApply (brel_fvt_of_int_correct_r (fin_val := CIPHER));
      first exact (int_of_fvt_of_int_sem (fin_val := CIPHER) (rv, c)).
    brel_pures_r.
    iModIntro. by iExists (rv, c).
  Qed.

  Lemma hyb_red_ideal : ⊢ sem_typed [] HYB (RED PIDEAL) ⊥ τE [].
  Proof.
    iIntros "!# %vs Hvs /=". rewrite /red_prf /pad_enc /enc_hyb.
    brel_pures_r. iModIntro. iSplitR "Hvs"; last done.
    iIntros (??) "(->&->)".
    brel_pures_l. brel_pures_r.
    brel_alloctape_l ιr as "Hιr". brel_pures_l.
    brel_alloctape_l ιp as "Hιp".
    iApply (brel_na_alloc (ιr ↪N (Z.to_nat (ns.(card) - 1); [])
                           ∗ ιp ↪N (Z.to_nat (ms.(card) - 1); []))%I (nroot .@ "hyb")).
    iSplitL "Hιr Hιp"; [iNext; iFrame|]. iIntros "#HI".
    brel_pures_l. rewrite /sem_ty_arr /sem_ty_mbang /=. iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    iApply (brel_na_inv _ _ (nroot .@ "hyb")); first set_solver.
    iFrame "HI". iIntros "((Hιr & Hιp) & Hclose)".
    brel_pures_l. brel_pures_r.
    rewrite /prf_ideal. brel_pures_r.
    brel_alloc_r ℓ as "Hℓ". brel_pures_r.
    (* the nonce *)
    rewrite /rand_nonce /rand_fvt. brel_pures_r.
    iApply (brel_couple_TU _ _ (λ x : fin _, x)).
    { by rewrite /=. }
    iSplitL "Hιr"; first (iNext; by iApply tapeN_to_empty).
    iIntros (r) "Hιr /=".
    iAssert (ιr ↪N (Z.to_nat (ns.(card) - 1); [fin_to_nat r]))%I with "[Hιr]" as "Hιr".
    { iExists [_]. simpl. iFrame. done. }
    brel_rand_l. brel_pures_l.
    pose proof (fin_to_nat_lt r) as Hr.
    destruct (fvt_of_int_sem_surj (FV := nonce) r) as (rv & Hrv & Hrv').
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_r (fin_val := nonce)); first done.
    brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := nonce)). brel_pures_r.
    brel_load_r. brel_pures_r.
    (* the pad, coupled with the oracle output along the inverse one-time pad *)
    rewrite /rand_prf_out /rand_fvt. brel_pures_r.
    set (k := int_of_fvt_sem (fin_val := msg) m).
    assert (S (Z.to_nat (ms.(card) - 1)) = N) as HN by (unfold fvt_of_fvts in *; simpl in *; lia).
    destruct (restr_bij_fin (S (Z.to_nat (ms.(card) - 1))) (pad_map N (N - k mod N))) as (g & Hg & Hgeq).
    { intros. rewrite HN in H0 |- *. by apply pad_map_lt. }
    iApply (brel_couple_TU _ _ g).
    { by rewrite /=. }
    iSplitL "Hιp"; first (iNext; by iApply tapeN_to_empty).
    iIntros (p) "Hιp /=".
    iAssert (ιp ↪N (Z.to_nat (ms.(card) - 1); [fin_to_nat p]))%I with "[Hιp]" as "Hιp".
    { iExists [_]. simpl. iFrame. done. }
    brel_rand_l. brel_pures_l.
    pose proof (fin_to_nat_lt p) as Hp.
    assert (Hp' : (fin_to_nat p < N)%nat) by lia.
    rewrite Hgeq.
    pose proof (pad_map_lt N (N - k mod N) p Hp') as Hy.
    destruct (fvt_of_int_sem_surj (FV := msg) (pad_map N (N - k mod N) p)) as (yv & Hyv & Hyv').
    { unfold fvt_of_fvts in *. simpl in *. lia. }
    iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first done.
    brel_pures_r. brel_load_r. brel_pures_r. brel_store_r. brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)).
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := msg)). brel_pures_r.
    iApply brel_na_close. iFrame "Hclose Hιr Hιp".
    rewrite Hyv' pad_code_Z; last lia.
    rewrite pad_map_inv //.
    destruct (fvt_of_int_sem_surj (FV := msg) p) as (pv & Hpv & Hpv'); first lia.
    iApply (brel_fvt_of_int_correct_r (fin_val := msg)); first done.
    brel_pures_r.
    rewrite -Hrv' -Hpv' -Nat2Z.inj_mul -Nat2Z.inj_add.
    iApply (brel_fvt_of_int_correct_l (fin_val := CIPHER));
      first exact (int_of_fvt_of_int_sem (fin_val := CIPHER) (rv, pv)).
    brel_pures_l.
    iModIntro. by iExists (rv, pv).
  Qed.

  (** The two-against-one coupling: the tapes of [HYB] against the [rand] of [enc_ideal]. *)
  Lemma hyb_ideal : ⊢ sem_typed [] HYB (enc_ideal SKES) ⊥ τE [].
  Proof.
    pose proof (@prod_fvt_card nt mt) as card_ct.
    iIntros "!# %vs Hvs /=". rewrite /enc_hyb /enc_ideal.
    iApply brel_value. iIntros "$ !>". iSplitL; last done.
    iIntros (??) "(->&->)".
    brel_pures_l. brel_pures_r.
    brel_alloctape_l ιr as "Hιr". brel_pures_l.
    brel_alloctape_l ιp as "Hιp".
    iApply (brel_na_alloc (ιr ↪N (Z.to_nat (ns.(card) - 1); [])
                           ∗ ιp ↪N (Z.to_nat (ms.(card) - 1); []))%I (nroot .@ "hyb")).
    iSplitL "Hιr Hιp"; [iNext; iFrame|]. iIntros "#HI".
    brel_pures_l. rewrite /sem_ty_arr /sem_ty_mbang /=. iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    iApply (brel_na_inv _ _ (nroot .@ "hyb")); first set_solver.
    iFrame "HI". iIntros "((Hιr & Hιp) & Hclose)".
    brel_pures_l. brel_pures_r. rewrite /rand_cipher /rand_fvt /=. brel_pures_r.
    iApply (brel_couple_TT_U (Z.to_nat (CS.(card) - 1)) (Z.to_nat (ns.(card) - 1)) (Z.to_nat (ms.(card) - 1))
              (λ r p, r * N + p)%nat).
    1-3: unfold fvt_of_fvts in *; simpl in *.
    1,3: intros; nia.
    { intros ????????. apply code_pair_inj; lia. }
    iFrame "Hιr Hιp".
    iIntros (n1 n2 Hn1 Hn2) "Hιr Hιp /=".
    brel_rand_l. brel_pures_l. brel_rand_l. brel_pures_l.
    iApply brel_na_close. iFrame "Hclose Hιr Hιp".
    rewrite -Nat2Z.inj_mul -Nat2Z.inj_add.
    destruct (fvt_of_int_sem_surj (FV := CIPHER) (n1 * N + n2)) as (c & Hc & _).
    { unfold fvt_of_fvts in *. simpl in *. rewrite card_ct. nia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := CIPHER)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := CIPHER)); first done.
    brel_pures_l. brel_pures_r.
    iModIntro. by iExists c.
  Qed.

  Lemma ideal_hyb : ⊢ sem_typed [] (enc_ideal SKES) HYB ⊥ τE [].
  Proof.
    pose proof (@prod_fvt_card nt mt) as card_ct.
    iIntros "!# %vs Hvs /=". rewrite /enc_hyb /enc_ideal.
    iApply brel_value. iIntros "$ !>". iSplitL; last done.
    iIntros (??) "(->&->)".
    brel_pures_l. brel_pures_r.
    brel_alloctape_r ιr as "Hιr". brel_pures_r.
    brel_alloctape_r ιp as "Hιp".
    iApply (brel_na_alloc (ιr ↪ₛ (Z.to_nat (ns.(card) - 1); [])
                           ∗ ιp ↪ₛ (Z.to_nat (ms.(card) - 1); []))%I (nroot .@ "hyb")).
    iSplitL "Hιr Hιp"; [iNext; iFrame|]. iIntros "#HI".
    brel_pures_r. rewrite /sem_ty_arr /sem_ty_mbang /=. iModIntro.
    iIntros (m1 m2) "!> (%m&->&->)".
    iApply (brel_na_inv _ _ (nroot .@ "hyb")); first set_solver.
    iFrame "HI". iIntros "((Hιr & Hιp) & Hclose)".
    brel_pures_l. brel_pures_r. rewrite /rand_cipher /rand_fvt /=. brel_pures_l.
    iApply (brel_couple_U_TT (Z.to_nat (CS.(card) - 1)) (Z.to_nat (ns.(card) - 1)) (Z.to_nat (ms.(card) - 1))
              (λ r p, r * N + p)%nat).
    1-3: unfold fvt_of_fvts in *; simpl in *.
    1,3: intros; nia.
    { intros ????????. apply code_pair_inj; lia. }
    iSplitL "Hιr"; first (iNext; by iApply empty_to_spec_tapeN).
    iSplitL "Hιp"; first (iNext; by iApply empty_to_spec_tapeN).
    iIntros "!>" (n1 n2 Hn1 Hn2) "Hιr Hιp /=".
    brel_rand_r. brel_pures_r. brel_rand_r. brel_pures_r.
    iApply brel_na_close. iFrame "Hclose".
    iSplitL "Hιr Hιp"; first (iNext; iSplitL "Hιr"; by iApply spec_tapeN_to_empty).
    rewrite -Nat2Z.inj_mul -Nat2Z.inj_add.
    destruct (fvt_of_int_sem_surj (FV := CIPHER) (n1 * N + n2)) as (c & Hc & _).
    { unfold fvt_of_fvts in *. simpl in *. rewrite card_ct. nia. }
    iApply (brel_fvt_of_int_correct_l (fin_val := CIPHER)); first done.
    iApply (brel_fvt_of_int_correct_r (fin_val := CIPHER)); first done.
    brel_pures_l. brel_pures_r.
    iModIntro. by iExists c.
  Qed.

End reduction_spec.

(** [advantage_reduction_expr] for an adversary that is an expression: after its
    argument [e0] is evaluated, [(λ: s, A (red s)) e0] steps purely to [A (red v)]. *)
Lemma advantage_reduction_adv_expr `{!probblazeRGpreS Σ} (s : string) (A : expr) (red : val)
    (e e' : expr) (b : bool) :
  (∀ v : val, val_subst s v A = A) →
  (∀ `{probblazeRGS Σ}, ∃ α β,
      (⊢ sem_typed [] A A ⊥ (β → 𝔹)%T []) /\
      (⊢ sem_val_typed red red (α → β)%T) /\
      (⊢ sem_typed [] e e ⊥ α []) /\ (⊢ sem_typed [] e' e' ⊥ α [])) →
  advantage A (red e) (red e') #b <= advantage (λ: s, A (red s)) e e' #b.
Proof.
  intros Hsub H.
  apply advantage_uniform => σ.
  etrans; last by apply (advantage_ub _ _ _ _ σ).
  right. unfold pr_dist.
  assert (∀ e0, (∀ (HRGS : probblazeRGS Σ), ∃ α β,
      (⊢ sem_typed [] A A ⊥ (β → 𝔹)%T []) /\
      (⊢ sem_val_typed red red (α → β)%T) /\
      (⊢ sem_typed [] e0 e0 ⊥ α [])) →
    lim_exec (A (red e0), σ) #b = lim_exec ((λ: s, A (red s))%E e0, σ) #b) as Heq.
  { intros e0 H0. f_equiv.
    apply ARcoupl_antisym; eapply brel_refines_coupling; try done; first last.
    - iIntros (HRGS). iStartProof.
      destruct (H0 HRGS) as (α & β & HA & Hred & He).
      iPoseProof He as "#He". iPoseProof Hred as "#Hred". iPoseProof HA as "#HA".
      iApply (brel_bind' [AppRCtx _] [AppRCtx _; AppRCtx _]); [iApply traversable_to_iThy_nil|].
      rewrite /sem_typed /tc_opaque /=.
      iDestruct ("He" $! ∅ with "[//]") as "He'". rewrite !fmap_empty !subst_map_empty.
      iApply (brel_wand with "He'").
      iIntros (v1 v2) "!# [Hα _] /=".
      iApply (brel_pure_step_later _ _ (fill [AppLCtx v1] (Val (RecV BAnon s (A (red s))))) _ True 1).
      { apply (pure_exec_ctx [AppLCtx v1] True 1 (Rec BAnon s _)). apply pure_recc. }
      { done. }
      iIntros "!> /=".
      iApply brel_pure_step_later; [done|iIntros "!> /="].
      rewrite Hsub decide_True //.
      rewrite /sem_val_typed /tc_opaque /sem_ty_arr /sem_ty_mbang /=.
      iDestruct "Hred" as "#Hred'".
      iApply (brel_bind' [AppRCtx A] [AppRCtx A]); [iApply traversable_to_iThy_nil|].
      iApply (brel_wand with "(Hred' Hα)").
      iIntros (w1 w2) "!# Hβ /=".
      iApply (brel_bind' [AppLCtx w1] [AppLCtx w2]); [iApply traversable_to_iThy_nil|].
      iDestruct ("HA" $! ∅ with "[//]") as "HA'". rewrite !fmap_empty !subst_map_empty.
      iApply (brel_mono OS _ _ [] [] with "[] HA' [Hβ]"); [iApply to_iThy_le_refl|].
      simpl. iIntros (f1 f2) "[#Hf _] /=". iApply ("Hf" with "Hβ").
    - by iIntros (???) "(%&->&->)".
    - iIntros (HRGS). iStartProof.
      destruct (H0 HRGS) as (α & β & HA & Hred & He).
      iPoseProof He as "#He". iPoseProof Hred as "#Hred". iPoseProof HA as "#HA".
      iApply (brel_bind' [AppRCtx _; AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy_nil|].
      rewrite /sem_typed /tc_opaque /=.
      iDestruct ("He" $! ∅ with "[//]") as "He'". rewrite !fmap_empty !subst_map_empty.
      iApply (brel_wand with "He'").
      iIntros (v1 v2) "!# [Hα _] /=".
      iApply (brel_pure_step_r _ _ _ (fill [AppLCtx v2] (Val (RecV BAnon s (A (red s))))) True 1).
      { apply (pure_exec_ctx [AppLCtx v2] True 1 (Rec BAnon s _)). apply pure_recc. }
      { done. }
      iApply brel_pure_step_r; [done|]. simpl.
      rewrite Hsub decide_True //.
      rewrite /sem_val_typed /tc_opaque /sem_ty_arr /sem_ty_mbang /=.
      iDestruct "Hred" as "#Hred'".
      iApply (brel_bind' [AppRCtx A] [AppRCtx A]); [iApply traversable_to_iThy_nil|].
      iApply (brel_wand with "(Hred' Hα)").
      iIntros (w1 w2) "!# Hβ /=".
      iApply (brel_bind' [AppLCtx w1] [AppLCtx w2]); [iApply traversable_to_iThy_nil|].
      iDestruct ("HA" $! ∅ with "[//]") as "HA'". rewrite !fmap_empty !subst_map_empty.
      iApply (brel_mono OS _ _ [] [] with "[] HA' [Hβ]"); [iApply to_iThy_le_refl|].
      simpl. iIntros (f1 f2) "[#Hf _] /=". iApply ("Hf" with "Hβ").
    - by iIntros (???) "(%&->&->)". }
  rewrite (Heq e); last (intros HRGS; destruct (H HRGS) as (α & β & ? & ? & ? & ?); by exists α, β).
  rewrite (Heq e'); last (intros HRGS; destruct (H HRGS) as (α & β & ? & ? & ? & ?); by exists α, β).
  done.
Qed.

Section reduction.
  Context {Σ : gFunctors} `{!probblazeRGpreS Σ}.
  Context {kt nt mt : fin_val_type}.
  Context {ks : @fin_val_type_struct kt} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.
  Context {key : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ _ ks} {nonce : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ _ ns}
          {msg : ∀ `{!probblazeRGS Σ}, @fin_val Σ _ _ ms}.
  Context {prf_struct : @PRF_struct kt nt mt ks ns ms}.
  Context {PRF_inst : ∀ `{!probblazeRGS Σ}, @PRF Σ _ kt nt mt ks ns ms (key _) (nonce _) (msg _) prf_struct}.
  Context `{!Inhabited (fvt_sort ks), !Inhabited (fvt_sort ns), !Inhabited (fvt_sort ms)}.

  Hypothesis kt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := kt))%nat.
  Hypothesis nt_nonempty : (1 ≤ fin_val_type.card (fin_val_type := nt))%nat.
  Hypothesis mt_nontriv : (2 ≤ fin_val_type.card (fin_val_type := mt))%nat.

  #[local] Notation SKES := (@prf_sym_struct kt nt mt ks ns ms prf_struct _ _ _).
  #[local] Notation RED := (@red_prf nt mt ns ms).
  #[local] Notation HYB := (@enc_hyb nt mt ns ms).
  #[local] Notation PREAL := (@prf_real kt nt mt ks ns ms prf_struct).
  #[local] Notation PIDEAL := (@prf_ideal nt mt ns ms).

  Definition τenc `{!probblazeRGS Σ} : sem_ty Σ :=
    (𝟙 ⊸ (sem_τFT (fin_val := msg _) → sem_τFT (fin_val := prod_fv (nonce _) (msg _))))%T.

  Lemma adv_enc_prf (A : expr) :
    (∀ v : val, val_subst "F" v A = A) →
    (∀ `{!probblazeRGS Σ}, ⊢ sem_typed [] A A ⊥ (τenc → 𝔹)%T []) →
    advantage A (enc_real SKES) (enc_ideal SKES) #true <=
      advantage (λ: "F", A (RED "F")) PREAL PIDEAL #true.
  Proof.
    intros Hsub HA.
    eapply (advantage_triangle _ _ (RED PREAL)).
    - right. eapply sem_typed_advantage_expr; first apply HA.
      split; intros; [by apply enc_real_red_real|by apply red_real_enc_real].
    - eapply (advantage_triangle _ _ (RED PIDEAL)).
      + apply (advantage_reduction_adv_expr "F"); first done. intros ?. eexists _, _.
        split; first apply HA. split; last split.
        * by iApply (red_prf_typed (PRF_inst := PRF_inst _)).
        * iApply compatibility.sem_typed_val. by iApply (prf_real_typed (PRF_inst := PRF_inst _)).
        * iApply compatibility.sem_typed_val. by iApply (prf_ideal_typed (PRF_inst := PRF_inst _)).
      + eapply (advantage_triangle _ _ HYB).
        * right. eapply sem_typed_advantage_expr; first apply HA.
          split; intros; [by apply red_ideal_hyb|by apply hyb_red_ideal].
        * right. eapply sem_typed_advantage_expr; first apply HA.
          split; intros; [by apply hyb_ideal|by apply ideal_hyb].
        * by rewrite Rplus_0_l.
      + by rewrite Rplus_0_r.
    - by rewrite Rplus_0_l.
  Qed.

End reduction.
