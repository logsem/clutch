(* Effects and handlers in the logic for equivalences.

   A label theory created during a proof is an [eqThy] built with
   [eq_thy_cons lls rls T X]: [lls] are the labels of [l], [rls] those of [r],
   and [T d] is the theory used in direction [d].  For a theory that relates
   an effect of [l] (left argument) to one of [r] (right argument), [T Bwd] is
   its mirror image; [eq_thy_app T el er Q] states [T] from [l]'s side.

   Labels of [l] and [r] are [lbl_l l] and [lbl_r l]; an unused one-shot
   continuation [r] of [l] is [r ↦ₗ #true] (the definition of [unshot]). *)

From iris.bi Require Import monpred.
From iris.proofmode Require Import base proofmode classes environments coq_tactics ltac_tactics reduction monpred.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode tactics notation.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic.

Section eq_handlers_defs.
  Context `{!probblazeRGS Σ}.

  Definition eq_thy_cons (lls rls : list label) (T : dir → iThy Σ) (X : eqThy Σ) : eqThy Σ :=
    EqThy (λ d, ((pick d lls rls, pick d rls lls), T d) :: eq_thy_at X d).

  (* [T] relating an effect [el] of [l] to an effect [er] of [r], with a
     continuation relation [Q] from [l]'s side. *)
  Definition eq_thy_app (T : dir → iThy Σ) (el er : expr) (Q : expr -d> expr -d> iProp Σ) : iPropD Σ :=
    MonPred (λ d, T d (pick d el er) (pick d er el) (λ s1 s2, Q (pick d s1 s2) (pick d s2 s1)))%I _.

  Definition eq_lbl_l (l : label) : iPropD Σ :=
    MonPred (λ d, match d with Fwd => is_label l (DfracOwn 1) | Bwd => spec_labels_frag l (DfracOwn 1) end)%I _.
  Definition eq_lbl_r (l : label) : iPropD Σ :=
    MonPred (λ d, match d with Fwd => spec_labels_frag l (DfracOwn 1) | Bwd => is_label l (DfracOwn 1) end)%I _.
End eq_handlers_defs.

Global Arguments eq_thy_app : simpl never.
#[local] Open Scope bi_scope.

Section eq_handlers.
  Context `{!probblazeRGS Σ}.
  Implicit Types (el er : expr) (X : eqThy Σ).

  (* ---------------------------------------------------------------- *)
  (* Theories.                                                          *)
  (* ---------------------------------------------------------------- *)

  Lemma eq_new_theory E el er X R :
    EQ el ≈ er @ E <|eq_thy_cons [] [] (λ _, iThyBot) X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof. split=> d. rewrite !eq_rel_at. iIntros "H". iApply brel_new_theory. by destruct d. Qed.

  Lemma eq_add_label_l E el er l lls rls X R :
    eq_lbl_l l ∗ EQ el ≈ er @ E <|eq_thy_cons (l :: lls) rls (λ _, iThyBot) X|> {{ R }}
    ⊢ EQ el ≈ er @ E <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep !eq_rel_at. iIntros "[Hl H]".
    destruct d; [iApply (brel_add_label_l with "Hl H")|iApply (brel_add_label_r with "Hl H")].
  Qed.

  Lemma eq_add_label_r E el er l lls rls X R :
    eq_lbl_r l ∗ EQ el ≈ er @ E <|eq_thy_cons lls (l :: rls) (λ _, iThyBot) X|> {{ R }}
    ⊢ EQ el ≈ er @ E <|eq_thy_cons lls rls (λ _, iThyBot) X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep !eq_rel_at. iIntros "[Hl H]".
    destruct d; [iApply (brel_add_label_r with "Hl H")|iApply (brel_add_label_l with "Hl H")].
  Qed.

  (* The labels of a theory have no duplicates. *)
  Lemma eq_learn_nodup el er lls rls T X R :
    (⌜NoDup lls ∧ NoDup rls⌝ -∗ EQ el ≈ er <|eq_thy_cons lls rls T X|> {{ R }})
    ⊢ EQ el ≈ er <|eq_thy_cons lls rls T X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_wand !eq_rel_at. iIntros "H".
    iApply brel_learn. iIntros ([Hdl Hdr]) "_".
    apply distinct_l_cons_inv in Hdl as [Hl _]. apply distinct_r_cons_inv in Hdr as [Hr _].
    iSpecialize ("H" $! d with "[//] []"); last (rewrite eq_rel_at; done).
    rewrite monPred_at_pure. iPureIntro. destruct d; simpl in *; tauto.
  Qed.

  (* The labels of [l] in the theory [X], in direction [d]. *)
  Definition eq_labels_l (X : eqThy Σ) (d : dir) : list label :=
    match d with Fwd => labels_l (eq_thy_at X Fwd) | Bwd => labels_r (eq_thy_at X Bwd) end.

  (* The labels of [l] in a theory have no duplicates; [P] is a consequence
     of this in each direction. *)
  Lemma eq_learn_labels_l el er X R (P : Prop) :
    (∀ d, NoDup (eq_labels_l X d) → P) →
    (⌜P⌝ -∗ EQ el ≈ er <|X|> {{ R }}) ⊢ EQ el ≈ er <|X|> {{ R }}.
  Proof.
    intros HP. split=> d. rewrite monPred_at_wand !eq_rel_at. iIntros "H".
    iApply brel_learn. iIntros ([Hdl Hdr]) "_".
    iSpecialize ("H" $! d with "[//] []"); last (rewrite eq_rel_at; done).
    rewrite monPred_at_pure. iPureIntro. destruct d; [apply (HP Fwd)|apply (HP Bwd)]; done.
  Qed.

  (* A larger theory, in each direction. *)
  Lemma eq_thy_mono el er X Y R :
    (∀ d, ⊢ to_iThy_le (eq_thy_at X d) (eq_thy_at Y d)) →
    EQ el ≈ er <|X|> {{ R }} ⊢ EQ el ≈ er <|Y|> {{ R }}.
  Proof.
    intros HXY. split=> d. rewrite !eq_rel_at. iIntros "H".
    iApply (brel_introduction_mono with "[] H"). iApply HXY.
  Qed.

  (* Handling the effects of [el] and [er] with a theory [T], under a theory
     [U] for the result. *)
  Lemma eq_exhaustion el er kl kr (T U : dir → iThy Σ) X R S lls rls :
    ectx_labels kl ⊆ lls → ectx_labels kr ⊆ rls →
    ⊢ EQ el ≈ er <|eq_thy_cons lls rls T X|> {{ R }} -∗
    ((□ ∀ vl vr, R vl vr -∗ EQ fill kl vl ≈ fill kr vr <|eq_thy_cons lls rls U X|> {{ S }})
     ∧
     (□ ∀ kl' kr' el' er' (Q : expr -d> expr -d> iProp Σ),
        ⌜NeutralEctx lls kl'⌝ -∗ ⌜NeutralEctx rls kr'⌝ -∗
        eq_thy_app T el' er' Q -∗
        (□ ▷ ∀ sl sr, ⎡Q sl sr⎤ -∗ EQ fill kl' sl ≈ fill kr' sr <|eq_thy_cons lls rls T X|> {{ R }}) -∗
        EQ fill (kl ++ kl') el' ≈ fill (kr ++ kr') er' <|eq_thy_cons lls rls U X|> {{ S }})) -∗
    EQ fill kl el ≈ fill kr er <|eq_thy_cons lls rls U X|> {{ S }}.
  Proof.
    intros Hkl Hkr. iStartProof (iProp _). iIntros (d) "H Hcases".
    iDestruct "Hcases" as "[#Hv #He]".
    iEval (rewrite eq_rel_at) in "H". rewrite eq_rel_at.
    destruct d; rewrite /pick /=.
    - iApply (brel_exhaustion with "H"); [done|done|]. iSplit.
      + iIntros "!>" (v1 v2) "HR". iApply (eq_rel_at_elim Fwd _ _ _ (eq_thy_cons lls rls U X)). by iApply "Hv".
      + iIntros "!>" (k1' k2' e1' e2' Q Hk1 Hk2) "HT #Hk".
        iApply (eq_rel_at_elim Fwd _ _ _ (eq_thy_cons lls rls U X)). iApply ("He" $! k1' k2' e1' e2' Q with "[//] [//] [HT]").
        { rewrite /eq_thy_app /=. iExact "HT". }
        iIntros "!> !>" (sl sr) "HQ". rewrite eq_rel_at /pick /=.
        by iApply "Hk".
    - iApply (brel_exhaustion with "H"); [done|done|]. iSplit.
      + iIntros "!>" (v1 v2) "HR". iApply (eq_rel_at_elim Bwd _ _ _ (eq_thy_cons lls rls U X)). by iApply ("Hv" $! v2 v1).
      + iIntros "!>" (k1' k2' e1' e2' Q Hk1 Hk2) "HT #Hk".
        iApply (eq_rel_at_elim Bwd _ _ _ (eq_thy_cons lls rls U X)).
        iApply ("He" $! k2' k1' e2' e1' (λ sl sr, Q sr sl) with "[//] [//] [HT]").
        { rewrite /eq_thy_app /=. iExact "HT". }
        iIntros "!> !>" (sl sr) "HQ". rewrite eq_rel_at /pick /=.
        by iApply "Hk".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Effects, handlers, continuations.                                  *)
  (* ---------------------------------------------------------------- *)

  Lemma eq_effect_l E K s e er X R :
    (∀ l, eq_lbl_l l ==∗ EQ fill K (lbl_subst s l e) ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (Effect s e) ≈ er @ E <|X|> {{ R }}.
  Proof.
    iStartProof (iProp _). iIntros (d) "H". rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply brel_effect_l. iIntros "!>" (l) "Hl".
      iMod ("H" $! l with "[Hl]") as "H"; first iExact "Hl". iModIntro. by iApply (eq_rel_at_elim Fwd).
    - iApply brel_effect_r. iIntros (l) "Hl".
      iMod ("H" $! l with "[Hl]") as "H"; first iExact "Hl". iModIntro. by iApply (eq_rel_at_elim Bwd).
  Qed.

  Lemma eq_effect_r E K s e el X R :
    (∀ l, eq_lbl_r l ==∗ EQ el ≈ fill K (lbl_subst s l e) @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (Effect s e) @ E <|X|> {{ R }}.
  Proof.
    iStartProof (iProp _). iIntros (d) "H". rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply brel_effect_r. iIntros (l) "Hl".
      iMod ("H" $! l with "[Hl]") as "H"; first iExact "Hl". iModIntro. by iApply (eq_rel_at_elim Fwd).
    - iApply brel_effect_l. iIntros "!>" (l) "Hl".
      iMod ("H" $! l with "[Hl]") as "H"; first iExact "Hl". iModIntro. by iApply (eq_rel_at_elim Bwd).
  Qed.

  Lemma eq_handle_os_l k k' hs (l : label) (v : val) (h ret : expr) er E X R :
    let c := match hs with Deep => HandleCtx hs OS l h ret :: k' | Shallow => k' end in
    l ∉ ectx_labels k' →
    (∀ r, r ↦ₗ #true -∗ EQ fill k (App (App h v) (ContV r c)) ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill k (Handle hs OS (EffLabel l) (fill k' (Do (EffLabel l) v)) h ret) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros c Hl. iStartProof (iProp _). iIntros (d) "H". rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply brel_handle_os_l; first done. iIntros "!>" (r) "Hr".
      iApply (eq_rel_at_elim Fwd). iApply ("H" $! r with "[Hr]"). iExact "Hr".
    - iApply brel_handle_os_r; first done. iIntros (r) "Hr".
      iApply (eq_rel_at_elim Bwd). iApply ("H" $! r with "[Hr]"). iExact "Hr".
  Qed.

  Lemma eq_handle_os_r k k' hs (l : label) (v : val) (h ret : expr) el E X R :
    let c := match hs with Deep => HandleCtx hs OS l h ret :: k' | Shallow => k' end in
    l ∉ ectx_labels k' →
    (∀ r, r ↦ᵣ #true -∗ EQ el ≈ fill k (App (App h v) (ContV r c)) @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill k (Handle hs OS (EffLabel l) (fill k' (Do (EffLabel l) v)) h ret) @ E <|X|> {{ R }}.
  Proof.
    intros c Hl. iStartProof (iProp _). iIntros (d) "H". rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply brel_handle_os_r; first done. iIntros (r) "Hr".
      iApply (eq_rel_at_elim Fwd). iApply ("H" $! r with "[Hr]"). iExact "Hr".
    - iApply brel_handle_os_l; first done. iIntros "!>" (r) "Hr".
      iApply (eq_rel_at_elim Bwd). iApply ("H" $! r with "[Hr]"). iExact "Hr".
  Qed.

  Lemma eq_cont_l k k' (v : val) (r : loc) er E X R :
    r ↦ₗ #true ∗ EQ fill k (fill k' v) ≈ er @ E <|X|> {{ R }}
    ⊢ EQ fill k (App (ContV r k') v) ≈ er @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep !eq_rel_at. iIntros "[Hr H]". destruct d; rewrite /pick /=.
    - by iApply (brel_cont_l with "Hr H").
    - by iApply (brel_cont_r with "Hr H").
  Qed.

  Lemma eq_cont_r k k' (v : val) (r : loc) el E X R :
    r ↦ᵣ #true ∗ EQ el ≈ fill k (fill k' v) @ E <|X|> {{ R }}
    ⊢ EQ el ≈ fill k (App (ContV r k') v) @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep !eq_rel_at. iIntros "[Hr H]". destruct d; rewrite /pick /=.
    - by iApply (brel_cont_r with "Hr H").
    - by iApply (brel_cont_l with "Hr H").
  Qed.

  (* Both programs handle an effect with a one-shot handler.  The left
     program's step gives a later in either direction, so the rule does too;
     this is what Löb induction over handled effects needs. *)
  Lemma eq_handle_os kl kl' kr kr' hsl hsr (ll lr : label) (vl vr : val) (hl hr retl retr : expr) E X R :
    let cl := match hsl with Deep => HandleCtx hsl OS ll hl retl :: kl' | Shallow => kl' end in
    let cr := match hsr with Deep => HandleCtx hsr OS lr hr retr :: kr' | Shallow => kr' end in
    ll ∉ ectx_labels kl' → lr ∉ ectx_labels kr' →
    ▷ (∀ rl rr, rl ↦ₗ #true -∗ rr ↦ᵣ #true -∗
         EQ fill kl (App (App hl vl) (ContV rl cl)) ≈ fill kr (App (App hr vr) (ContV rr cr)) @ E <|X|> {{ R }})
    ⊢ EQ fill kl (Handle hsl OS (EffLabel ll) (fill kl' (Do (EffLabel ll) vl)) hl retl)
       ≈ fill kr (Handle hsr OS (EffLabel lr) (fill kr' (Do (EffLabel lr) vr)) hr retr) @ E <|X|> {{ R }}.
  Proof.
    intros cl cr Hl Hr. iStartProof (iProp _). iIntros (d) "H". rewrite eq_rel_at. destruct d; rewrite /pick /=.
    - iApply brel_handle_os_l; first done. iIntros "!>" (rl) "Hrl".
      iApply brel_handle_os_r; first done. iIntros (rr) "Hrr".
      iApply (eq_rel_at_elim Fwd). iApply ("H" $! rl rr with "[Hrl] [Hrr]"); [iExact "Hrl"|iExact "Hrr"].
    - iApply brel_handle_os_l; first done. iIntros "!>" (rr) "Hrr".
      iApply brel_handle_os_r; first done. iIntros (rl) "Hrl".
      iApply (eq_rel_at_elim Bwd). iApply ("H" $! rl rr with "[Hrl] [Hrr]"); [iExact "Hrl"|iExact "Hrr"].
  Qed.

  (* Both programs resume a one-shot continuation; like [eq_handle_os], this
     gives a later in either direction. *)
  Lemma eq_cont kl kl' kr kr' (vl vr : val) (rl rr : loc) E X R :
    rl ↦ₗ #true ∗ rr ↦ᵣ #true ∗ ▷ EQ fill kl (fill kl' vl) ≈ fill kr (fill kr' vr) @ E <|X|> {{ R }}
    ⊢ EQ fill kl (App (ContV rl kl') vl) ≈ fill kr (App (ContV rr kr') vr) @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite !monPred_at_sep monPred_at_later !eq_rel_at. iIntros "(Hl & Hr & H)".
    destruct d; rewrite /pick /=.
    - iApply (brel_cont_l with "Hl"). iNext. by iApply (brel_cont_r with "Hr H").
    - iApply (brel_cont_l with "Hr"). iNext. by iApply (brel_cont_r with "Hl H").
  Qed.

  (* Binding in contexts [kl], [kr] whose labels are those of a theory [M]:
     the inner computation runs under [Y], the outer one under [X], which
     contains [Y] and [M]. *)
  Lemma eq_bind_gen kl kr (Y M X : eqThy Σ) el er R :
    (∀ d, ectx_labels (pick d kl kr) ⊆ labels_l (eq_thy_at M d)) →
    (∀ d, ectx_labels (pick d kr kl) ⊆ labels_r (eq_thy_at M d)) →
    (∀ d, ⊢ to_iThy_le (eq_thy_at Y d ++ eq_thy_at M d) (eq_thy_at X d)) →
    EQ el ≈ er <|Y|> {{ λ vl vr, EQ fill kl vl ≈ fill kr vr <|X|> {{ R }} }}
    ⊢ EQ fill kl el ≈ fill kr er <|X|> {{ R }}.
  Proof.
    intros Hl Hr HX. split=> d. rewrite !eq_rel_at. iIntros "H".
    destruct d; rewrite /pick /=.
    - iApply (brel_bind'' _ _ (eq_thy_at Y Fwd) (eq_thy_at M Fwd)); [apply (Hl Fwd)|apply (Hr Fwd)|iApply (HX Fwd)|].
      iApply (brel_wand with "H"). iIntros "!>" (v1 v2) "H". by rewrite eq_rel_at /pick /=.
    - iApply (brel_bind'' _ _ (eq_thy_at Y Bwd) (eq_thy_at M Bwd)); [apply (Hl Bwd)|apply (Hr Bwd)|iApply (HX Bwd)|].
      iApply (brel_wand with "H"). iIntros "!>" (v1 v2) "H". by rewrite eq_rel_at /pick /=.
  Qed.

  (** Symmetric theories *)

  (* A theory is symmetric if, seen backwards, it relates the same effects,
     with the programs swapped and the continuation relation flipped. *)
  Definition eq_thy_sym (T : dir → iThy Σ) : Prop :=
    ∀ e1 e2 (Q : expr -d> expr -d> iProp Σ), T Bwd e2 e1 (λ s1 s2, Q s2 s1) ⊣⊢ T Fwd e1 e2 Q.

  (* A theory built from one constructor, applied to the labels of [l]
     first, is symmetric if the constructor is invariant under swapping. *)
  Lemma eq_thy_sym_pick {A} (mk : A → A → iThy Σ) (a b : A) :
    (∀ e1 e2 (Q : expr -d> expr -d> iProp Σ), mk b a e2 e1 (λ s1 s2, Q s2 s1) ⊣⊢ mk a b e1 e2 Q) →
    eq_thy_sym (λ d, mk (pick d a b) (pick d b a)).
  Proof. intros H e1 e2 Q. apply H. Qed.

  (* A symmetric theory, as the program [l] sees it. *)
  Lemma eq_thy_app_sym T el er Q :
    eq_thy_sym T → eq_thy_app T el er Q ⊣⊢ ⎡T Fwd el er Q⎤.
  Proof.
    intros HT. split=> d. rewrite monPred_at_embed /eq_thy_app /=.
    destruct d; rewrite /pick /=; [done|apply HT].
  Qed.

  (* Performing effects [el], [er] that [T], at labels [lls], [rls] of [X],
     relates, in neutral contexts [kl], [kr]. *)
  Lemma eq_introduction lls rls (T : dir → iThy Σ) X kl kr el er R (Q : expr -d> expr -d> iProp Σ) :
    (∀ d, ((pick d lls rls, pick d rls lls), T d) ∈ eq_thy_at X d) →
    NeutralEctx lls kl → NeutralEctx rls kr →
    ⊢ eq_thy_app T el er Q -∗
      (□ ∀ sl sr, ⎡Q sl sr⎤ -∗ EQ fill kl sl ≈ fill kr sr <|X|> {{ R }}) -∗
      EQ fill kl el ≈ fill kr er <|X|> {{ R }}.
  Proof.
    intros Hin Hkl Hkr. iStartProof (iProp _). iIntros (d) "HT #Hk". rewrite eq_rel_at.
    iApply brel_introduction'; first apply (Hin d).
    iExists (pick d el er), (pick d er el), (pick d kl kr), (pick d kr kl), (λ s1 s2, Q (pick d s1 s2) (pick d s2 s1)).
    rewrite /eq_thy_app /=.
    destruct d; rewrite /pick /=; (do 4 (iSplit; [done|])); iFrame "HT".
    - iIntros "!>" (s1 s2) "HQ". iApply (eq_rel_at_elim Fwd _ _ _ X). by iApply ("Hk" $! s1 s2).
    - iIntros "!>" (s1 s2) "HQ". iApply (eq_rel_at_elim Bwd _ _ _ X). by iApply ("Hk" $! s2 s1).
  Qed.
End eq_handlers.

(* ------------------------------------------------------------------ *)
(* Proof-mode lemmas and tactics.                                     *)
(* ------------------------------------------------------------------ *)

Section eq_handlers_tactics.
  Context `{!probblazeRGS Σ}.
  Implicit Types (el er : expr) (Δ : envs (iPropD Σ)) (X : eqThy Σ).

  Lemma tac_eq_effect_l E K Δ e s el er X R :
    IntoCtx el (TCEq (Effect s e)) K →
    envs_entails Δ (∀ l, eq_lbl_l l ==∗ EQ fill K (lbl_subst s l e) ≈ er @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK HΔ. apply tc_eq_fill in HK. rewrite -HK HΔ. apply eq_effect_l. Qed.

  Lemma tac_eq_effect_r E K Δ e s el er X R :
    IntoCtx er (TCEq (Effect s e)) K →
    envs_entails Δ (∀ l, eq_lbl_r l ==∗ EQ el ≈ fill K (lbl_subst s l e) @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK HΔ. apply tc_eq_fill in HK. rewrite -HK HΔ. apply eq_effect_r. Qed.

  Lemma tac_eq_handle_os_l E K K' l hs h ret Δ el er v X R :
    let c := match hs with Deep => HandleCtx hs OS l h ret :: K' | Shallow => K' end in
    IntoCtx el (TCEq (Handle hs OS l (fill K' (do: l (of_val v))) h ret)) K →
    l ∉ ectx_labels K' →
    envs_entails Δ (∀ r : loc, r ↦ₗ #true -∗ EQ fill K (h v (ContV r c)) ≈ er @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> c HK Hl HΔ. apply tc_eq_fill in HK. rewrite -HK HΔ.
    by apply eq_handle_os_l.
  Qed.

  Lemma tac_eq_handle_os_r E K K' l hs h ret Δ el er v X R :
    let c := match hs with Deep => HandleCtx hs OS l h ret :: K' | Shallow => K' end in
    IntoCtx er (TCEq (Handle hs OS l (fill K' (do: l (of_val v))) h ret)) K →
    l ∉ ectx_labels K' →
    envs_entails Δ (∀ r : loc, r ↦ᵣ #true -∗ EQ el ≈ fill K (h v (ContV r c)) @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> c HK Hl HΔ. apply tc_eq_fill in HK. rewrite -HK HΔ.
    by apply eq_handle_os_r.
  Qed.

  Lemma tac_eq_cont_l E K K' Δ Δ' i (r : loc) (v : val) el el' er X R :
    IntoCtx el (TCEq (App (ContV r K') v)) K →
    envs_lookup_delete false i Δ = Some (false, r ↦ₗ #true, Δ')%I →
    el' = fill K (fill K' v) →
    envs_entails Δ' (EQ el' ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK Hlk -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_lookup_delete_sound //=. iIntros "[Hr HΔ]". iApply eq_cont_l. iFrame "Hr". by iApply HΔ.
  Qed.

  Lemma tac_eq_cont_r E K K' Δ Δ' i (r : loc) (v : val) el er er' X R :
    IntoCtx er (TCEq (App (ContV r K') v)) K →
    envs_lookup_delete false i Δ = Some (false, r ↦ᵣ #true, Δ')%I →
    er' = fill K (fill K' v) →
    envs_entails Δ' (EQ el ≈ er' @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK Hlk -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_lookup_delete_sound //=. iIntros "[Hr HΔ]". iApply eq_cont_r. iFrame "Hr". by iApply HΔ.
  Qed.

  Lemma tac_eq_handle_os E Kl Kl' Kr Kr' ll lr hsl hsr hl hr retl retr Δ Δ' el er vl vr X R :
    let cl := match hsl with Deep => HandleCtx hsl OS ll hl retl :: Kl' | Shallow => Kl' end in
    let cr := match hsr with Deep => HandleCtx hsr OS lr hr retr :: Kr' | Shallow => Kr' end in
    IntoCtx el (TCEq (Handle hsl OS ll (fill Kl' (do: ll (of_val vl))) hl retl)) Kl →
    IntoCtx er (TCEq (Handle hsr OS lr (fill Kr' (do: lr (of_val vr))) hr retr)) Kr →
    ll ∉ ectx_labels Kl' → lr ∉ ectx_labels Kr' →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_entails Δ' (∀ rl rr : loc, rl ↦ₗ #true -∗ rr ↦ᵣ #true -∗
      EQ fill Kl (hl vl (ContV rl cl)) ≈ fill Kr (hr vr (ContV rr cr)) @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> cl cr HKl HKr Hl Hr HΔ' HΔ.
    apply tc_eq_fill in HKl. apply tc_eq_fill in HKr. rewrite -HKl -HKr.
    rewrite into_laterN_env_sound HΔ /=. by apply eq_handle_os.
  Qed.

  Lemma tac_eq_cont E Kl Kl' Kr Kr' Δ Δ' Δ1 Δ2 il ir (rl rr : loc) (vl vr : val) el el' er er' X R :
    IntoCtx el (TCEq (App (ContV rl Kl') vl)) Kl →
    IntoCtx er (TCEq (App (ContV rr Kr') vr)) Kr →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup_delete false il Δ' = Some (false, rl ↦ₗ #true, Δ1)%I →
    envs_lookup_delete false ir Δ1 = Some (false, rr ↦ᵣ #true, Δ2)%I →
    el' = fill Kl (fill Kl' vl) → er' = fill Kr (fill Kr' vr) →
    envs_entails Δ2 (EQ el' ≈ er' @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HKl HKr ? Hl Hr -> -> HΔ.
    apply tc_eq_fill in HKl. apply tc_eq_fill in HKr. rewrite -HKl -HKr.
    rewrite into_laterN_env_sound envs_lookup_delete_sound //= envs_lookup_delete_sound //=.
    rewrite HΔ. iIntros "H". iDestruct "H" as "(>Hl & >Hr & H)". iApply eq_cont. iFrame.
  Qed.

End eq_handlers_tactics.

Tactic Notation "eq_effect_l" simple_intropattern(l) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_effect_l;
    [ tc_solve || fail "eq_effect_l: no effect allocation in l"
    | simpl; iIntros (l) H; iModIntro ]).

Tactic Notation "eq_effect_r" simple_intropattern(l) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_effect_r;
    [ tc_solve || fail "eq_effect_r: no effect allocation in r"
    | simpl; iIntros (l) H; iModIntro ]).

Tactic Notation "eq_handle_os_l" simple_intropattern(r) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_handle_os_l;
    [ tc_solve || fail "eq_handle_os_l: no one-shot handler in l"
    | try eapply neutral_ectx; repeat constructor
    | simpl; iIntros (r) H ]).

Tactic Notation "eq_handle_os_r" simple_intropattern(r) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_handle_os_r;
    [ tc_solve || fail "eq_handle_os_r: no one-shot handler in r"
    | try eapply neutral_ectx; repeat constructor
    | simpl; iIntros (r) H ]).

Tactic Notation "eq_cont_l" :=
  eq_goal_check ltac:(
    eapply tac_eq_cont_l;
    [ tc_solve || fail "eq_cont_l: no one-shot continuation in l"
    | let r := match goal with |- _ = Some (_, eq_pt_l ?r _ _, _) => r end in
      iAssumptionCore || fail "eq_cont_l: cannot find" r "↦ₗ #true"
    | reflexivity
    | simpl ]).

Tactic Notation "eq_cont_r" :=
  eq_goal_check ltac:(
    eapply tac_eq_cont_r;
    [ tc_solve || fail "eq_cont_r: no one-shot continuation in r"
    | let r := match goal with |- _ = Some (_, eq_pt_r ?r _ _, _) => r end in
      iAssumptionCore || fail "eq_cont_r: cannot find" r "↦ᵣ #true"
    | reflexivity
    | simpl ]).

(* [eq_handle_os rl rr as "Hl" "Hr"]: both programs handle an effect; laters
   in the context are stripped. *)
Tactic Notation "eq_handle_os" simple_intropattern(rl) simple_intropattern(rr) "as" constr(Hl) constr(Hr) :=
  eq_goal_check ltac:(
    eapply tac_eq_handle_os;
    [ tc_solve || fail "eq_handle_os: no one-shot handler in l"
    | tc_solve || fail "eq_handle_os: no one-shot handler in r"
    | try eapply neutral_ectx; repeat constructor
    | try eapply neutral_ectx; repeat constructor
    | tc_solve
    | simpl; iIntros (rl rr); iIntros Hl; iIntros Hr ]).

(* [eq_exhaustion el er]: handle the effects of [el] and [er], in their
   evaluation contexts. *)
Tactic Notation "eq_exhaustion" open_constr(el) open_constr(er) :=
  eq_reshape_l el; eq_reshape_r er; iApply (eq_exhaustion el er).

(* [eq_handle_os_l_in K']: apply [eq_handle_os_l] to the handler whose body
   is [fill K' (do: l v)], wherever it is in [l]; the side condition on the
   labels of [K'] comes first.  [eq_handle_os_in Kl' Kr'] does the same on
   both sides with [eq_handle_os]. *)
Tactic Notation "eq_handle_os_l_in" open_constr(K') :=
  eq_reshape_l (Handle _ OS (EffLabel _) (fill K' (Do (EffLabel _) (Val _))) _ _);
  iApply (eq_handle_os_l _ K').

Tactic Notation "eq_handle_os_r_in" open_constr(K') :=
  eq_reshape_r (Handle _ OS (EffLabel _) (fill K' (Do (EffLabel _) (Val _))) _ _);
  iApply (eq_handle_os_r _ K').

Tactic Notation "eq_handle_os_in" open_constr(Kl') open_constr(Kr') :=
  eq_reshape_l (Handle _ OS (EffLabel _) (fill Kl' (Do (EffLabel _) (Val _))) _ _);
  eq_reshape_r (Handle _ OS (EffLabel _) (fill Kr' (Do (EffLabel _) (Val _))) _ _);
  iApply (eq_handle_os _ Kl' _ Kr').

Tactic Notation "eq_exhaustion" open_constr(el) open_constr(er) "with" constr(pat) :=
  eq_reshape_l el; eq_reshape_r er; iApply (eq_exhaustion el er with pat).

(* [eq_cont]: both programs resume a one-shot continuation; laters in the
   context are stripped. *)
Tactic Notation "eq_cont" :=
  eq_goal_check ltac:(
    eapply tac_eq_cont;
    [ tc_solve || fail "eq_cont: no one-shot continuation in l"
    | tc_solve || fail "eq_cont: no one-shot continuation in r"
    | tc_solve
    | let r := match goal with |- _ = Some (_, eq_pt_l ?r _ _, _) => r end in
      iAssumptionCore || fail "eq_cont: cannot find" r "↦ₗ #true"
    | let r := match goal with |- _ = Some (_, eq_pt_r ?r _ _, _) => r end in
      iAssumptionCore || fail "eq_cont: cannot find" r "↦ᵣ #true"
    | reflexivity
    | reflexivity
    | simpl ]).
