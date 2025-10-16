From iris.prelude Require Import options.

From iris.algebra Require Import list.
From iris.proofmode  Require Export base tactics classes proofmode.

From clutch.approxis Require Export app_weakestpre.

From clutch.prelude Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Export spec_rules class_instances primitive_laws.
From clutch.prob_eff_lang.probblaze Require Import  notation syntax notation semantics.

Import uPred.

(* Taken from the blaze logic *)
(* Omitted the iThyMono since we don't have one shots for now *)
(* ========================================================================= *)
(* Relational Theories. *)

Section theories.
  Context `{!probblazeGS Σ}.
  Implicit Types Φ : val -d> val -d> iProp Σ.

  (* ----------------------------------------------------------------------- *)
  (* Domain of theories. *)

  Definition iThy Σ := expr -d> expr -d> (expr -d> expr -d> iProp Σ) -n> iProp Σ.

  (* ----------------------------------------------------------------------- *)
  (* Theory sum. *)

  Program Definition iThySum (X Y : iThy Σ) : iThy Σ := (λ a1 a2, λne Q,
    X a1 a2 Q ∨ Y a1 a2 Q
  )%I.
  Next Obligation. solve_proper. Qed.
  Global Instance iThySum_ne : NonExpansive2 iThySum.
  Proof.
    rewrite /iThySum=> n ?? H ?? H' ?? Q /=.
    f_equiv; [apply (H _ _ _)|apply (H' _ _ _)].
  Qed.
  Global Instance iThySum_proper : Proper ((≡) ==> (≡) ==> (≡)) iThySum.
  Proof. apply: ne_proper_2. Qed.

  (* ----------------------------------------------------------------------- *)
  (* Empty theory. *)

  Definition iThyBot : iThy Σ := λ _ _, λne _, False%I.

  (* ----------------------------------------------------------------------- *)
  (* Domain of theory list. *)

  Definition iLblThy Σ := list ((list label * list label) * iThy Σ)%type.

  (* ----------------------------------------------------------------------- *)
  (* Context-closure operator. *)

  Program Definition iThyTraverse (l1s l2s : list label) (X : iThy Σ) : iThy Σ :=
  (λ e1 e2, λne Q,
    ∃ e1' e2' k1 k2 S,
      ⌜ e1 = fill k1 e1' ⌝ ∗ ⌜ NeutralEctx l1s k1 ⌝ ∗
      ⌜ e2 = fill k2 e2' ⌝ ∗ ⌜ NeutralEctx l2s k2 ⌝ ∗
      X e1' e2' S ∗ □ ∀ s1 s2, S s1 s2 -∗ Q (fill k1 s1) (fill k2 s2)
  )%I.
  Next Obligation. solve_proper. Qed.
  Global Instance iThyTraverse_ne l1s l2s : NonExpansive (iThyTraverse l1s l2s).
  Proof. intros n ?? H ???. rewrite /iThyTraverse /=. do 16 f_equiv. apply (H _ _). Qed.
  Global Instance iThyTraverse_proper l1s l2s : Proper ((≡) ==> (≡)) (iThyTraverse l1s l2s).
  Proof. apply: ne_proper. Qed.

  (* ----------------------------------------------------------------------- *)
  (* Make every theory in a list [L] empty. *)

  Definition to_iThy_bot (L : iLblThy Σ) : iLblThy Σ :=
    map (λ '((l1s, l2s), _), ((l1s, l2s), iThyBot)) L.
  Global Instance to_iThy_bot_ne : NonExpansive to_iThy_bot.
  Proof.
    intros n ?? H. rewrite /to_iThy_bot /=.
    apply list_fmap_ne; last done.
    by intros [[? ?] ?] [[? ?] ?] [-> ?]%pair_dist_inj.
  Qed.
  Global Instance to_iThy_bot_proper : Proper ((≡) ==> (≡)) to_iThy_bot.
  Proof. apply: ne_proper. Qed.

  (* ----------------------------------------------------------------------- *)
  (* Interpretation of theory lists. *)

  Program Definition to_iThy (L : iLblThy Σ) : iThy Σ := (λ e1 e2, λne Q,
    ∃ l1s l2s X, ⌜ ((l1s, l2s), X) ∈ L ⌝ ∗ iThyTraverse l1s l2s X e1 e2 Q
  )%I.
  Next Obligation. solve_proper. Qed.

  Lemma to_iThy_cons l1s l2s X L e1 e2 Q :
    to_iThy (((l1s, l2s), X) :: L) e1 e2 Q ⊣⊢
    iThySum (iThyTraverse l1s l2s X) (to_iThy L) e1 e2 Q.
  Proof.
    iSplit.
    - iIntros "(%l1s' & %l2s' & %Y & %Hin & HY)".
      rewrite elem_of_cons in Hin.
      destruct Hin as [HX|HL].
      + inversion HX. simplify_eq. by iLeft.
      + iRight. iExists l1s', l2s', Y. by iFrame.
    - iIntros "[HX|(%l1s' & %l2s' & %Y & %Hin & HY)]".
      + iExists l1s, l2s, X. iFrame. iPureIntro.
        by rewrite elem_of_cons; left.
      + iExists l1s', l2s', Y. iFrame. iPureIntro.
        by rewrite elem_of_cons; right.
  Qed.

  Global Instance to_iThy_ne : NonExpansive to_iThy.
  Proof.
    intros n L L' H. revert L H.
    induction L' as [|[[l1s' l2s'] X'] L' IH]; intros.
    - by apply nil_dist_eq in H as ->.
    - apply cons_dist_eq in H as
        ([[l1s l2s] X] & L'' & [[Hl1s Hl2s]%pair_dist_inj HX]%pair_dist_inj & HL & ->).
      intros e1 e2 Q.
      rewrite !to_iThy_cons.
      refine (iThySum_ne n _ _ _ _ _ _ e1 e2 Q).
      + apply discrete, leibniz_equiv in Hl1s as ->, Hl2s as ->; [|tc_solve..].
        by rewrite HX.
      + by apply IH.
  Qed.
  Global Instance to_iThy_proper : Proper ((≡) ==> (≡)) to_iThy.
  Proof. apply: ne_proper. Qed.

  (* ----------------------------------------------------------------------- *)
  (* Theory ordering. *)

  Definition iThy_le (X Y : iThy Σ) : iProp Σ :=
    □ ∀ e1 e2 Q, X e1 e2 Q -∗ Y e1 e2 Q.

  (* ----------------------------------------------------------------------- *)
  (* Properties of theory ordering. *)

  Global Instance iThy_le_ne : NonExpansive2 iThy_le.
  Proof.
    rewrite /iThy_le=> n ?? H ?? H'.
    repeat f_equiv; [apply (H _ _)|apply (H' _ _)].
  Qed.
  Global Instance iThy_le_proper : Proper ((≡) ==> (≡) ==> (≡)) iThy_le.
  Proof. apply: ne_proper_2. Qed.

  Lemma iThy_le_refl (X : iThy Σ) : ⊢ iThy_le X X.
  Proof. by iIntros "!>" (???) "?". Qed.

  Lemma iThy_le_trans (X Y Z : iThy Σ) :
    iThy_le X Y -∗ iThy_le Y Z -∗ iThy_le X Z.
  Proof. by iIntros "#HXY #HYZ !> %%% HX"; iApply "HYZ"; iApply "HXY". Qed.

  Lemma iThy_le_bot (X : iThy Σ) : ⊢ iThy_le iThyBot X.
  Proof. by iIntros (???) "!> ?". Qed.

  Lemma iThy_le_sum_swap (X Y : iThy Σ) :
    ⊢ iThy_le (iThySum X Y) (iThySum Y X).
  Proof. by iIntros "!> %%% [?|?]"; [iRight|iLeft]. Qed.

  Lemma iThy_le_sum_assoc_1 (X Y Z : iThy Σ) :
    ⊢ iThy_le (iThySum X (iThySum Y Z)) (iThySum (iThySum X Y) Z).
  Proof.
    by iIntros "!> %%% [?|[?|?]]"; [iLeft; iLeft | iLeft; iRight | iRight].
  Qed.

  Lemma iThy_le_sum_assoc_2 (X Y Z : iThy Σ) :
    ⊢ iThy_le (iThySum (iThySum X Y) Z) (iThySum X (iThySum Y Z)).
  Proof.
    by iIntros "!> %%% [[?|?]|?]"; [iLeft | iRight; iLeft | iRight; iRight].
  Qed.

  Lemma iThy_le_sum_map X X' Y Y' :
    iThy_le X X' -∗ iThy_le Y Y' -∗ iThy_le (iThySum X Y) (iThySum X' Y').
  Proof.
    by iIntros "#HX' #HY' !> %%% [?|?]"; [iLeft; iApply "HX'"|iRight; iApply "HY'"].
  Qed.

  Lemma iThy_le_sum_1 X Y Z :
    iThy_le X Z -∗ iThy_le Y Z -∗ iThy_le (iThySum X Y) Z.
  Proof. by iIntros "#HX' #HY' !> %%% [?|?]"; [iApply "HX'"|iApply "HY'"]. Qed.

  Lemma iThy_le_sum_2 X Y Z :
    iThy_le (iThySum X Y) Z -∗ iThy_le X Z ∧ iThy_le Y Z.
  Proof.
    by iIntros "#Hle"; iSplit; iIntros "!> %e1 %e2 %Q H";
    iApply "Hle"; [iLeft|iRight].
  Qed.

  Lemma iThy_le_sum_l X Y Z : iThy_le X Y -∗ iThy_le (iThySum X Z) (iThySum Y Z).
  Proof. iIntros "H"; iApply (iThy_le_sum_map with "H"); iApply iThy_le_refl. Qed.

  Lemma iThy_le_sum_r X Y Z : iThy_le X Y -∗ iThy_le (iThySum Z X) (iThySum Z Y).
  Proof. iIntros "H"; iApply (iThy_le_sum_map with "[] H"); iApply iThy_le_refl. Qed.

  Lemma iThy_le_sum_l_2 X Y : ⊢ iThy_le X (iThySum X Y).
  Proof. by iIntros (???) "!> ?"; iLeft. Qed.

  Lemma iThy_le_sum_r_2 X Y : ⊢ iThy_le X (iThySum Y X).
  Proof. by iIntros (???) "!> ?"; iRight. Qed.

  Lemma iThy_le_to_iThy_nil X : ⊢ iThy_le (to_iThy []) X.
  Proof. iIntros (???) "!> [% [% [% [% _]]]]"; set_solver. Qed.

  Lemma iThy_le_sum_bot_l X : ⊢ iThy_le (iThySum iThyBot X) X.
  Proof. by iIntros "!> %%% [?|?]". Qed.

  Lemma iThy_le_sum_bot_r X : ⊢ iThy_le (iThySum X iThyBot) X.
  Proof. by iIntros "!> %%% [?|?]". Qed.

  Lemma iThyTraverse_bot l1s l2s e1 e2 Q :
    iThyTraverse l1s l2s iThyBot e1 e2 Q ⊣⊢ False.
  Proof.
    iSplit; [|by iIntros "?"].
    by iIntros "(% & % & % & % & % & _ & _ & _ & _ & ? & _)".
  Qed.

  Lemma iThy_le_iThyTraverse_bot X l1s l2s : ⊢ iThy_le (iThyTraverse l1s l2s iThyBot) X.
  Proof. iIntros "!> %%% ?". by rewrite iThyTraverse_bot. Qed.

  Lemma to_iThy_nil : to_iThy [] ≡ iThyBot.
  Proof.
    intros e1 e2 Q.
    iSplit; [|by iIntros "?"].
    iIntros "(%opt_l1 & %opt_l2 & %X & %Hin & _)".
    by inversion Hin.
  Qed.
  
  (* ----------------------------------------------------------------------- *)
  (* Traversable predicate. *)

  Definition traversable (k1 k2 : ectx) (X : iThy Σ) : iProp Σ :=
    □ ∀ e1 e2 Q, X e1 e2 Q -∗ ∃ Q',
          X (fill k1 e1) (fill k2 e2) Q' ∗
          □ ∀ s1 s2, Q' s1 s2 -∗ ∃ s1' s2',
                ⌜ s1 = fill k1 s1' ⌝ ∗
                ⌜ s2 = fill k2 s2' ⌝ ∗
                Q s1' s2'.
  Global Instance traversable_proper k1 k2 : Proper ((≡) ==> (≡)) (traversable k1 k2).
  Proof. intros ?? H. rewrite /traversable. repeat f_equiv; apply (H _ _). Qed.

  (* ----------------------------------------------------------------------- *)
  (* Properties of the traversable predicate. *)

  Lemma traversable_bot k1 k2 : ⊢ traversable k1 k2 iThyBot.
  Proof. by iIntros "!>" (???) "?". Qed.

  Lemma traversable_sum X Y k1 k2 :
    traversable k1 k2 X -∗
    traversable k1 k2 Y -∗
    traversable k1 k2 (iThySum X Y).
  Proof.
    iIntros "#HX #HY !>" (e1 e2 Q) "[HX'|HY']".
    - iDestruct ("HX" with "HX'") as "[%Q' [HX' #HQ']]".
      by iExists Q'; iSplit; [iLeft|].
    - iDestruct ("HY" with "HY'") as "[%Q' [HY' #HQ']]".
      by iExists Q'; iSplit; [iRight|].
  Qed.

  Lemma traversable_le X Y k1 k2 :
    iThy_le X Y -∗ iThy_le Y X -∗
    traversable k1 k2 X -∗ traversable k1 k2 Y.
  Proof.
    iIntros "#HXY #HYX #HX !>" (e1 e2 Q) "HY".
    iSpecialize ("HYX" with "HY").
    iDestruct ("HX" with "HYX") as "[%Q' [? ?]]".
    iExists Q'. by iSplit; [iApply "HXY"|].
  Qed.

  Lemma traversable_iThyTraverse l1s l2s X k1 k2 :
    NeutralEctx l1s k1 →
    NeutralEctx l2s k2 →
    ⊢ traversable k1 k2 (iThyTraverse l1s l2s X).
  Proof.
    iIntros (Hk1 Hk2). iIntros "!>" (e1 e2 Q)
      "(%e1'&%e2'&%k1'&%k2'&%S&%He1&%Hk1'&%He2&%Hk2'&HX&#HQ)".
    iExists (λ s1 s2, ∃ s1' s2',
      ⌜ s1 = fill k1 s1' ⌝ ∗
      ⌜ s2 = fill k2 s2' ⌝ ∗
      Q s1' s2'
    )%I.
    iSplit; [|by iIntros "!>" (??) "?"].
    iExists e1', e2', (k1 ++ k1'), (k2 ++ k2'), S.
    rewrite He1 He2 //=.
    iSplit; [|iSplit; [|iSplit; [|iSplit]]]; try iPureIntro.
    { by rewrite fill_app. } { by apply NeutralEctx_app. }
    { by rewrite fill_app. } { by apply NeutralEctx_app. }
    iFrame. iModIntro. iIntros (s1 s2) "?".
    iExists (fill k1' s1), (fill k2' s2).
    iSplit; [|iSplit]; try by rewrite fill_app.
    by iApply "HQ".
  Qed.

End theories.

(* ========================================================================= *)
(* baze: The Base logic. *)

(* ------------------------------------------------------------------------- *)
(* Model. *)

Section rel.
  Context `{!probblazeGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (* Observational refinement. *)

  (* TODO: add error credits somewhere *)

  Definition obs_refines_def :
    coPset -d> expr -d> expr -d> (val -d> val -d> iProp Σ) -d> iProp Σ := (λ E e1 e2 R, ∀ k,
    ⤇ fill k e2 -∗
    |={E, ⊤}=> WP e1 {{ v1, ∃ (v2 : val), ⤇ fill k (of_val v2) ∗ R v1 v2 }})%I.
  Definition obs_refines_aux : seal obs_refines_def. Proof. by eexists. Qed.
  Definition obs_refines := unseal obs_refines_aux.
  Definition obs_refines_eq : obs_refines = obs_refines_def :=
    seal_eq obs_refines_aux.

  Global Instance obs_refines_ne E e1 e2 : NonExpansive (obs_refines E e1 e2).
  Proof. rewrite obs_refines_eq /obs_refines_def. solve_proper. Qed.
  Global Instance obs_refines_proper E e1 e2 : Proper ((≡) ==> (≡)) (obs_refines E e1 e2).
  Proof. apply: ne_proper. Qed.

  (* ----------------------------------------------------------------------- *)
  (* Validation of a theory by a pair of contextxs. *)

  Definition kwp_pre
    (rel : coPset -d> expr -d> expr -d> iThy Σ -d> (val -d> val -d> iProp Σ) -d> iProp Σ) :
    (val -d> val -d> iProp Σ) -d>
    ectx -d> ectx -d> iThy Σ -d>
    (val -d> val -d> iProp Σ) -d> iProp Σ
  := (λ R k1 k2 X S,
    (* Value case. *)
    (∀ v1 v2, R v1 v2 -∗ obs_refines ⊤ (fill k1 v1) (fill k2 v2) S)
      ∧
    (* Effect case. *)
    (∀ e1 e2 Q,
      X e1 e2 Q -∗
      □ ▷ (∀ s1 s2, Q s1 s2 -∗ rel ⊤ s1 s2 X R) -∗
      obs_refines ⊤ (fill k1 e1) (fill k2 e2) S
    )
     )%I.

   (* ----------------------------------------------------------------------- *)
  (* Refinement (before fixpoint). *)

  Definition rel_pre :
   (coPset -d> expr -d> expr -d> iThy Σ -d> (val -d> val -d> iProp Σ) -d> iProp Σ) →
   (coPset -d> expr -d> expr -d> iThy Σ -d> (val -d> val -d> iProp Σ) -d> iProp Σ)
  := (λ rel E e1 e2 X R,
    ∀ k1 k2 S,
      (kwp_pre rel R k1 k2 X S -∗ obs_refines E (fill k1 e1) (fill k2 e2) S)
  )%I.

  Local Instance kwp_pre_contractive : Contractive kwp_pre.
  Proof.
    rewrite /kwp_pre => n rel rel' Hdist R k1 k2 X S. f_equiv.
    repeat (f_contractive || f_equiv).
    by apply Hdist.
  Qed.

  Local Instance rel_pre_contractive : Contractive rel_pre.
  Proof.
    rewrite /rel_pre => n rel rel' Hdist E e1 e2 X R.
    repeat (f_contractive || f_equiv). by apply kwp_pre_contractive.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* Definition of [rel] -- Refinement relation as a fixpoint. *)

  Definition rel_def := fixpoint rel_pre.
  Definition rel_aux : seal rel_def. Proof. by eexists. Qed.
  Definition rel := rel_aux.(unseal).

  (* ----------------------------------------------------------------------- *)
  (* Definition of [kwp]. *)

  Definition kwp := kwp_pre rel.

  (* ----------------------------------------------------------------------- *)
  (* Rewriting principle for [rel]. *)

  Definition rel_eq : rel = rel_def := rel_aux.(seal_eq).
  Global Lemma rel_unfold E e1 e2 X R : rel E e1 e2 X R ⊣⊢ rel_pre rel E e1 e2 X R.
  Proof. by rewrite rel_eq /rel_def; apply (fixpoint_unfold rel_pre). Qed.

  Global Instance rel_ne E e1 e2 : NonExpansive2 (rel E e1 e2).
  Proof.
    intros n. revert E e1 e2.
    induction (lt_wf n) as [n _ IH]=> E e1 e2 X Y HXY R S HRS.
    rewrite !rel_unfold /rel_pre /kwp_pre.
    do 16 f_equiv. { apply (HXY _ _). }
    f_equiv. f_contractive. do 5 f_equiv. apply IH; first done.
    - eapply dist_le; [apply HXY|].
      by apply Nat.lt_le_incl.
    - eapply dist_le; [apply HRS|].
      by apply Nat.lt_le_incl.
  Qed.
  Global Instance rel_proper E e1 e2 : Proper ((≡) ==> (≡) ==> (≡)) (rel E e1 e2).
  Proof. apply: ne_proper_2. Qed.

  Global Instance kwp_ne n :
    Proper (dist n ==> (=) ==> (=) ==> dist n ==> dist n ==> dist n) kwp.
  Proof.
    rewrite /kwp /kwp_pre.
    intros R R' HR k1 ? <- k2 ? <- X X' HX S S' HS.
    do 6 f_equiv; try solve_proper.
    do 3 f_equiv; try solve_proper.
    apply (HX _ _).
  Qed.

  Global Instance kwp_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (≡) ==> (≡) ==> (≡)) kwp.
  Proof.
    intros ???????????????.
    apply equiv_dist=>n.
    apply kwp_ne; auto using equiv_dist.
  Qed.

End rel.


(* ------------------------------------------------------------------------- *)
(* Notation. *)

Notation "'REL' e1 ≤ e2 @ E <| X | > {{ R } }" :=
  (rel E e1%E e2%E X%I R%I)
  (at level 20, E, e1, e2, X, R at next level, only parsing) : bi_scope.

Notation "'REL' e1 ≤ e2 <| X | > {{ R } }" :=
  (rel ⊤ e1%E e2%E X%I R%I)
  (at level 20, e1, e2, X, R at next level, only parsing) : bi_scope.

(* Notation "'REL' e1 ≤ e2 @ E  <| X | > {{ v1 ; v2 , Q } }" :=
     (rel E e1%E e2%E X%I (λ v1 v2, Q)%I)
     (at level 20, E, e1, e2, X, Q at next level,
     format "'[hv' 'REL'  e1  ≤  e2 @ E  '/' <| X | >  '/' {{  '[' v1  ;  v2 ,  '/' Q  ']' } } ']'") : bi_scope. *)

(* Notation "'REL' e1 ≤ e2  <| X | > {{ v1 ; v2 , Q } }" :=
     (rel ⊤ e1%E e2%E X%I (λ v1 v2, Q)%I)
     (at level 20, e1, e2, X, Q at next level,
     format "'[hv' 'REL'  e1  ≤  e2   '/' <| X | >  '/' {{  '[' v1  ;  v2 ,  '/' Q  ']' } } ']'") : bi_scope. *)




(* ------------------------------------------------------------------------- *)
(* baze: Reasoning rules. *)

Section baze_rules.
  Context `{!probblazeGS Σ}.

  Implicit Types X Y Z : iThy Σ.

  Lemma obs_refines_value (v1 v2 : val) R : R v1 v2 -∗ obs_refines ⊤ v1 v2 R.
  Proof.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros "HR" (k) "Hj".
    iApply wp_value.
    iExists v2. by iFrame.
  Qed.

  Lemma kwp_empty R : ⊢ kwp R [] [] iThyBot R.
  Proof.
    iSplit.
    - iIntros (v1 v2) "HR". by iApply obs_refines_value.
    - by iIntros (???) "?".
  Qed.

  Lemma rel_value (v1 v2 : val) X (R : val -d> val -d> iProp Σ) : R v1 v2 ⊢ REL v1 ≤ v2 <|X|> {{ R }}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros "HR" (k1 k2 S) "[Hvalue _]".
    by iApply "Hvalue".
  Qed.
  
  Lemma fupd_obs_refines E1 E2 e1 e2 R :
    (|={E1, E2}=> obs_refines E2 e1 e2 R) ⊢ obs_refines E1 e1 e2 R.
  Proof.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros "H" (k) "Hj". iMod "H" as "H".
    by iApply ("H" with "Hj").
  Qed.

  Lemma fupd_rel' E1 E2 e1 e2 X R :
    (|={E1, E2}=> REL e1 ≤ e2 @ E2 <|X|> {{R}}) ⊢ REL e1 ≤ e2 @ E1 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros "Hrel" (k1 k2 S) "Hkwp".
    rewrite obs_refines_eq /obs_refines_def.
    iIntros (k) "Hj".
    iMod "Hrel" as "Hrel".
    by iSpecialize ("Hrel" with "Hkwp Hj").
  Qed.

  Lemma fupd_rel e1 e2 X R : (|={⊤}=> REL e1 ≤ e2 <|X|> {{R}}) ⊢ REL e1 ≤ e2 <|X|> {{R}}.
  Proof. apply fupd_rel'. Qed.

  Lemma rel_introduction e1 e2 Q X R :
    X e1 e2 Q -∗
    □ ▷ (∀ s1 s2, Q s1 s2 -∗ REL s1 ≤ s2 <|X|> {{R}}) -∗
    REL e1 ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros "HX #HQ" (k1 k2 S). iIntros "[_ Hprot]".
    by iApply ("Hprot" with "HX").
  Qed.

  Lemma rel_introduction' e1 e2 X R :
    X e1 e2 (λ s1 s2, REL s1 ≤ s2 <|X|> {{R}}) ⊢ REL e1 ≤ e2 <|X|> {{R}}.
  Proof. iIntros "HX". by iApply (rel_introduction with "HX"); auto. Qed.

  Lemma rel_introduction_mono e1 e2 X Y R :
    REL e1 ≤ e2 <|X|> {{R}} -∗ iThy_le X Y -∗ REL e1 ≤ e2 <|Y|> {{R}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    rewrite !rel_unfold /rel_pre.
    iIntros "Hrel #Hle %k1 %k2 %S Hkwp".
    iApply "Hrel". clear e1 e2.
    iSplit.
    - iIntros (v1 v2) "HR". by iApply "Hkwp".
    - iIntros (e1 e2 Q) "HX #Hrel".
      iApply ("Hkwp" with "[HX]").
      { iApply ("Hle" with "HX"). }
      iIntros "!> !> %% HQ".
      iSpecialize ("Hrel" with "HQ").
      iApply ("IH" with "Hrel Hle").
  Qed.

  Lemma rel_atomic_l (E : coPset) K e1 e2 X R
        (Hatomic : Atomic StronglyAtomic e1) :
   (|={⊤,E}=> WP e1 @ E {{ v,
     REL fill K (of_val v) ≤ e2 @ E <|X|> {{R}} }})%I -∗
   REL fill K e1 ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros "Hlog".
    iIntros (k1 k2 S) "Hkwp".
    iIntros (k) "Hj /=". iModIntro.
    rewrite -!fill_app.
    iApply wp_bind. iApply wp_atomic; auto.
    iMod "Hlog" as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    rewrite !rel_unfold /rel_pre.
    rewrite obs_refines_eq /obs_refines_def.
    rewrite !fill_app.
    by iSpecialize ("Hlog" with "Hkwp Hj").
  Qed.

  Definition closeInv N P : iProp Σ := ▷ P ={⊤ ∖ ↑N, ⊤}=∗ True.

  Lemma rel_inv_restore N P e1 e2 X R :
   closeInv N P -∗
   ▷ P -∗
   REL e1 ≤ e2 <|X|> {{R}} -∗
   REL e1 ≤ e2 @ (⊤ ∖ ↑N) <|X|> {{R}}.
  Proof.
    iIntros "Hclose HP Hrel".
    iSpecialize ("Hclose" with "HP").
    iApply (fupd_rel' (⊤ ∖ ↑N) ⊤).
    iMod "Hclose" as "Hclose".
    by iModIntro.
  Qed.

  (* Lemma rel_inv_alloc N P e1 e2 X R :
      ▷ P -∗
      (inv N P -∗ REL e1 ≤ e2 <|X|> {{R}}) -∗
      REL e1 ≤ e2 <|X|> {{R}}.
     Proof.
       iIntros "HP Hrel".
       iApply fupd_rel.
       iMod (inv_alloc N ⊤ P with "HP") as "Hinv".
       iModIntro.
       by iApply "Hrel".
     Qed. *)
  
  Lemma rel_wand' e1 e2 X Y R S :
    iThy_le X Y -∗
    REL e1 ≤ e2 <|X|> {{R}} -∗
    (□ ∀ v1 v2, R v1 v2 -∗ S v1 v2) -∗
    REL e1 ≤ e2 <|Y|> {{S}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    rewrite !rel_unfold /rel_pre.
    iIntros "#HY Hrel #Hle %k1 %k2 %T Hkwp".
    iApply "Hrel".
    iSplit.
    - iIntros (v1 v2) "HR". iApply "Hkwp". by iApply "Hle".
    - iIntros (e1' e2' Q) "HX #Hrel".
      iApply ("Hkwp" with "[HX]"). { by iApply "HY". }
      iIntros "!> !> %% HQ".
      iSpecialize ("Hrel" with "HQ").
      by iApply ("IH" with "HY Hrel").
  Qed.

  Lemma rel_wand e1 e2 X R S :
    REL e1 ≤ e2 <|X|> {{R}} -∗
    (□ ∀ v1 v2, R v1 v2 -∗ S v1 v2) -∗
    REL e1 ≤ e2 <|X|> {{S}}.
  Proof. iApply rel_wand'. by iApply iThy_le_refl. Qed.

  Lemma rel_introduction_sum_mono_l e1 e2 X Y Z R :
    REL e1 ≤ e2 <|iThySum X Z|> {{R}} -∗
    iThy_le X Y -∗
    REL e1 ≤ e2 <|iThySum Y Z|> {{R}}.
  Proof.
    iIntros "Hrel Hle".
    iApply (rel_introduction_mono with "Hrel").
    iApply (iThy_le_sum_l with "Hle").
  Qed.

  Lemma rel_introduction_sum_mono_r e1 e2 X Y Z R :
    REL e1 ≤ e2 <|iThySum Z X|> {{R}} -∗
    iThy_le X Y -∗
    REL e1 ≤ e2 <|iThySum Z Y|> {{R}}.
  Proof.
    iIntros "Hrel Hle".
    iApply (rel_introduction_mono with "Hrel").
    iApply (iThy_le_sum_r with "Hle").
  Qed.

  Lemma rel_exhaustion k1 k2 e1 e2 X Y R S :
    REL e1 ≤ e2 <|X|> {{R}} -∗

    ((∀ v1 v2, R v1 v2 -∗ REL fill k1 v1 ≤ fill k2 v2 <|Y|> {{S}})

       ∧

     (∀ e1' e2' Q,
       X e1' e2' Q -∗
       □ ▷ (∀ s1 s2, Q s1 s2 -∗ REL s1 ≤ s2 <|X|> {{R}}) -∗
       REL fill k1 e1' ≤ fill k2 e2' <|Y|> {{S}})
    ) -∗

    REL fill k1 e1 ≤ fill k2 e2 <|Y|> {{S}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros "Hrel Hfill".
    iIntros (k1' k2' T) "HK".
    rewrite -!fill_app.
    iApply "Hrel".
    iSplit.
    - iIntros (v1 v2) "HR".
      iSpecialize ("Hfill" with "HR").
      rewrite !rel_unfold /rel_pre !fill_app.
      by iApply "Hfill".
    - iIntros (e1' e2' Q) "HX #HQ".
      iSpecialize ("Hfill" with "HX HQ").
      rewrite !rel_unfold /rel_pre.
      iSpecialize ("Hfill" $! k1' k2').
      rewrite -!fill_app.
      by iApply "Hfill".
  Qed.

  Lemma rel_exhaustion_sum_l k1 k2 e1 e2 X Y Z R S :
    traversable k1 k2 X -∗

    REL e1 ≤ e2 <|iThySum X Y|> {{R}} -∗

    □ ((∀ v1 v2, R v1 v2 -∗ REL fill k1 v1 ≤ fill k2 v2 <|iThySum X Z|> {{S}})

         ∧

       (∀ e1' e2' Q,
         Y e1' e2' Q -∗
         □ ▷ (∀ s1 s2, Q s1 s2 -∗ REL s1 ≤ s2 <|iThySum X Y|> {{R}}) -∗
         REL fill k1 e1' ≤ fill k2 e2' <|iThySum X Z|> {{S}})
    ) -∗

    REL fill k1 e1 ≤ fill k2 e2 <|iThySum X Z|> {{S}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    iIntros "#HX' Hrel #Hfill".
    iApply (rel_exhaustion with "Hrel").
    iSplit; [iIntros (??) "HS"; by iApply "Hfill"|].
    clear e1 e2.
    iIntros (e1 e2 Q) "[HX|HY] #Hk"; [|by iApply ("Hfill" with "HY")].
    iDestruct ("HX'" with "HX") as "(%Q'&HX&#HQ)".
    iApply (rel_introduction with "[HX]"). { iLeft. by iApply "HX". }
    iIntros "!> !>" (s1 s2) "HQ'".
    iDestruct ("HQ" with "HQ'") as "(%s1'&%s2'&%Hs1&%Hs2&H)".
    rewrite Hs1 Hs2 //=.
    iSpecialize ("Hk" with "H").
    by iApply ("IH" with "[//] Hk").
  Qed.

  Lemma rel_bind k1 k2 e1 e2 X Y R :
    traversable k1 k2 X -∗
    iThy_le X Y -∗
    REL e1 ≤ e2 <|X|> {{ (λ v1 v2, REL fill k1 v1 ≤ fill k2 v2 <|Y|> {{R}} )}} -∗
    REL fill k1 e1 ≤ fill k2 e2 <|Y|> {{R}}.
  Proof.
    iIntros "#Htrav #Hle He12".
    iLöb as "IH" forall (e1 e2).
    iApply (rel_exhaustion with "He12"). iSplit; first auto.
    iIntros (???) "HX #Hk".
    iDestruct ("Htrav" with "HX") as "(%Q' & HX & #HQ)".
    iDestruct ("Hle" with "HX") as "HY".
    iApply (rel_introduction with "HY").
    iIntros "!> !> %% HQ'". clear e1 e2.
    iDestruct ("HQ" with "HQ'") as "[%e1 [%e2 (-> & -> & H)]]".
    iApply "IH". by iApply "Hk".
  Qed.

  Lemma rel_bind' k1 k2 e1 e2 X R :
    traversable k1 k2 X -∗
    REL e1 ≤ e2 <|X|> {{ (λ v1 v2, REL fill k1 v1 ≤ fill k2 v2 <|X|> {{R}}) }} -∗
    REL fill k1 e1 ≤ fill k2 e2 <|X|> {{R}}.
  Proof. iIntros "#HX". by iApply rel_bind; last iApply iThy_le_refl. Qed.

  Lemma rel_introduction_sum_swap e1 e2 X Y R :
    REL e1 ≤ e2 <|iThySum X Y|> {{R}} -∗ REL e1 ≤ e2 <|iThySum Y X|> {{R}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    rewrite !rel_unfold /rel_pre.
    iIntros "Hrel" (k1 k2 S) "HK".
    iApply "Hrel".
    iSplit; [by iDestruct "HK" as "[$ _]"|].
    iIntros (???) "HXY #Hrel".
    iDestruct "HXY" as "[HX|HY]".
    - iApply ("HK" with "[HX]"). { by iRight. }
      iIntros "!> !>" (??) "HQ".
      iSpecialize ("Hrel" with "HQ").
      by iApply "IH".
    - iApply ("HK" with "[HY]"). { by iLeft. }
      iIntros "!> !>" (??) "HQ".
      iSpecialize ("Hrel" with "HQ").
      by iApply "IH".
  Qed.

  Lemma rel_introduction_sum_l e1 e2 X Y R :
    REL e1 ≤ e2 <|X|> {{R}} -∗ REL e1 ≤ e2 <|iThySum X Y|> {{R}}.
  Proof.
    iLöb as "IH" forall (e1 e2).
    rewrite !rel_unfold /rel_pre.
    iIntros "Hrel" (k1 k2 S) "HK".
    iApply "Hrel".
    iSplit; [by iDestruct "HK" as "[$ _]"|].
    iIntros (???) "HX #Hrel".
    iApply ("HK" with "[HX]"). { by iLeft. }
    iIntros "!> !>" (??) "HQ".
    iSpecialize ("Hrel" with "HQ").
    by iApply "IH".
  Qed.

  Lemma rel_introduction_sum_r e1 e2 X Y R :
    REL e1 ≤ e2 <|Y|> {{R}} -∗ REL e1 ≤ e2 <|iThySum X Y|> {{R}}.
  Proof. by iIntros "?"; iApply rel_introduction_sum_swap; iApply rel_introduction_sum_l. Qed.

  Lemma obs_refines_pure_step_l e1 e1' e2 φ n S :
    φ →
    PureExec φ n e1 e1' →
    ▷^n (obs_refines ⊤ e1' e2 S) -∗ obs_refines ⊤ e1 e2 S.
  Proof.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros (Hφ Hexec) "He1' %k2 Hj".
    iModIntro.
    iApply wp_pure_step_later; [done|].
    iIntros "!>".
    iApply fupd_wp.
    by iApply "He1'".
  Qed.

  (* Lemma obs_refines_pure_step_r_with_mask E e1 e2 e2' φ n S :
       φ →
       PureExec φ n e2 e2' →
       obs_refines E e1 e2' S -∗ obs_refines E e1 e2 S.
     Proof.
       rewrite obs_refines_eq /obs_refines_def.
       iIntros (Hφ Hexec) "He1' %k2 Hj".
       iApply spec_update_wp.
       iMod (step_pure with "Hj") as "Hj"; first done.
       { by apply Hexec. }
       by iApply "He1'".
     Qed. *)

  Lemma obs_refines_pure_step_r e1 e2 e2' φ n S :
    φ →
    PureExec φ n e2 e2' →
    obs_refines ⊤ e1 e2' S -∗ obs_refines ⊤ e1 e2 S.
  Proof. (* by apply obs_refines_pure_step_r_with_mask. Qed. *)
    rewrite obs_refines_eq /obs_refines_def.
    iIntros (Hφ Hexec) "He1' %k2 Hj". iModIntro.
    iMod (step_pure with "Hj") as "Hj"; first done.
    iApply fupd_wp.
    iApply "He1'". done.
  Qed.

  Lemma pure_step_ctx K e1 e2 :
    pure_step e1 e2 → pure_step (fill K e1) (fill K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. intros σ1.
      destruct (Hred σ1) as [[]].
      exists (fill K e, s). simpl in H. rewrite -(fill_step_prob K); eauto using val_prim_stuck, prim_step_uncaught_eff. 
    - intros σ.
      rewrite -fill_step_prob //;
                 [apply (val_prim_stuck _ σ (e2, σ))|eapply (prim_step_uncaught_eff _ σ e2 σ)];
        rewrite (Hstep σ); lra.
  Qed.

  Lemma pure_step_nsteps_ctx K n e1 e2 :
    nsteps pure_step n e1 e2 →
    nsteps pure_step n (fill K e1) (fill K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma pure_exec_ctx K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  Lemma rel_pure_step_l e1 e1' e2 X φ n R :
    φ →
    PureExec φ n e1 e1' →
    ▷^n ( REL e1' ≤ e2 <|X|> {{R}}) ⊢ REL e1 ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros (Hφ Hexec) "Hrel"; iIntros (k1 k2 S) "Hkwp".
    iApply (obs_refines_pure_step_l (fill k1 e1) (fill k1 e1')).
    { by apply Hφ. }
    { by apply pure_exec_ctx. }
    { iIntros "!>". iApply ("Hrel" with "Hkwp"). }
  Qed.

  Lemma rel_pure_step_l' e1 e1' e2 φ n X R :
    PureExec φ n e1 e1' →
    φ →
    ▷^n (REL e1' ≤ e2 <|X|> {{R}}) ⊢ REL e1 ≤ e2 <|X|> {{R}}.
  Proof. by intros ??; apply (rel_pure_step_l _ _ _ _ φ). Qed.

  (* Lemma rel_pure_step_r_with_mask E e1 e2 e2' φ n X R :
       ↑specN ⊆ E →
       PureExec φ n e2 e2' →
       φ →
       REL e1 ≤ e2' @ E <|X|> {{R}} ⊢ REL e1 ≤ e2 @ E <|X|> {{R}}.
     Proof.
       rewrite !rel_unfold /rel_pre.
       iIntros (HE Hexec Hφ) "Hrel"; iIntros (k1 k2 S) "Hkwp".
       iApply (obs_refines_pure_step_r_with_mask _ _ (fill k2 e2) (fill k2 e2')).
       { by apply HE. }
       { by apply Hφ. }
       { by apply pure_exec_fill. }
       { by iApply "Hrel". }
     Qed. *)

  Lemma rel_pure_step_r e1 e2 e2' X φ n R :
    φ →
    PureExec φ n e2 e2' →
    REL e1 ≤ e2' <|X|> {{R}} ⊢ REL e1 ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros (Hφ Hexec) "Hrel"; iIntros (k1 k2 S) "Hkwp".
    iApply (obs_refines_pure_step_r _ (fill k2 e2) (fill k2 e2')).
    { by apply Hφ. }
    { by apply pure_exec_ctx. }
    { by iApply "Hrel". }
  Qed.

  Lemma rel_pure_step_r' e1 e2 e2' φ n X R :
    PureExec φ n e2 e2' →
    φ →
    REL e1 ≤ e2' <|X|> {{R}} ⊢ REL e1 ≤ e2 <|X|> {{R}}.
  Proof. by intros ??; apply (rel_pure_step_r _ _ e2' _ φ n). Qed.

  Lemma rel_effect_l X s1 e1 e2 R :
    ▷ (∀ l1, primitive_laws.is_label l1 (DfracOwn 1) ==∗ REL lbl_subst s1 l1 e1 ≤ e2 <|X|> {{R}}) -∗
    REL Effect s1 e1 ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel" (k1' k2' S) "Hkwp %k2 Hj".
    iApply wp_effect. iModIntro.
    iIntros "!> %l1 Hl1".
    iMod ("Hrel" with "Hl1") as "Hrel".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def. 
    by iApply ("Hrel" with "Hkwp Hj").
  Qed.

  Lemma rel_effect_r X R e1 k2 s2 e2 :
    (∀ l2, spec_labels_frag l2 (DfracOwn 1) ==∗ REL e1 ≤ fill k2 (lbl_subst s2 l2 e2) <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (Effect s2 e2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    rewrite -!fill_app. iModIntro.
    iMod (step_alloc_label with "Hj") as (l) "[Hj Hl]".
    rewrite !fill_app.
    iMod ("Hrel" with "Hl") as "Hrel".
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iApply fupd_wp.
    iApply ("Hrel" with "Hkwp Hj").
  Qed.

  (* Lemma rel_allocN_l X R k1 (n1 : Z) v1 e2 :
       (0 < n1)%Z →
       ▷ (∀ l1,
           ([∗ list] i ∈ seq 0 (Z.to_nat n1),
             (l1 +ₗ (i : nat))%E ↦ v1
            ) -∗
           REL fill k1 #l1 ≤ e2 <|X|> {{R}}) -∗
       REL fill k1 (AllocN #n1 v1) ≤ e2 <|X|> {{R}}.
     Proof.
       rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
       iIntros "%Hgt_0 Hrel %k1' %k2' %S Hkwp %j %k2'' #Hspec Hj".
       iEval (rewrite -fill_app).
       iApply wp_allocN; first done. iModIntro.
       iIntros "!> %l1 Hpoints_to".
       iSpecialize ("Hrel" with "Hpoints_to").
       rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq fill_app.
       iApply fupd_wp.
       by iApply ("Hrel" with "Hkwp Hspec Hj").
     Qed. *)

  Lemma rel_alloc_l X R k1 v1 e2 :
    ▷ (∀ l1, l1 ↦ v1 -∗  REL fill k1 #l1 ≤ e2 <|X|> {{R}}) -∗
    REL fill k1 (ref v1) ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    iEval (rewrite -fill_app).
    iApply wp_bind.
    iApply wp_alloc; first done. iModIntro.
    iIntros "!> %l1 Hpoints_to".
    iSpecialize ("Hrel" with "Hpoints_to").
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq fill_app.
    iApply fupd_wp.
    by iApply ("Hrel" with "Hkwp Hj").
  Qed.

  Lemma rel_alloc_r X R e1 k2 v2 :
    (∀ l2, l2 ↦ₛ v2 -∗ REL e1 ≤ fill k2 #l2 <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (ref v2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    rewrite -!fill_app.
    iModIntro.
    iMod (step_alloc with "Hj") as (l2) "[Hj Hl2]".
    iSpecialize ("Hrel" with "Hl2").
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq !fill_app.
    iApply fupd_wp.
    iApply ("Hrel" with "Hkwp Hj").
  Qed.

  Lemma rel_load_l X R k1 l1 dq1 v1 e2 :
    ▷ l1 ↦{dq1} v1 -∗
    ▷ (l1 ↦{dq1} v1 -∗ REL fill k1 v1 ≤ e2 <|X|> {{R}}) -∗
    REL fill k1 (! #l1) ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl1 Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    iEval (rewrite -fill_app).
    iApply wp_bind.
    iApply (wp_load with "Hl1").
    iIntros "!> !> Hl1". rewrite fill_app.
    iApply fupd_wp.
    iApply ("Hrel" with "Hl1 Hkwp Hj").
  Qed.

  Lemma rel_load_l_inv' K E l q e2 X R :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') ≤ e2 @ E <|X|> {{R}})))%I
    ⊢ REL fill K (! #l) ≤ e2 <|X|> {{R}}.
  Proof.
    iIntros "Hrel".
    iApply (rel_atomic_l E). iMod "Hrel" as "[%v [Hl Hrel]]". iModIntro.
    iApply (wp_load with "Hl"). iNext. iIntros "Hl".
    by iApply "Hrel".
  Qed.

  (* Lemma rel_load_l_inv N P K l q e2 X R :
       inv N P -∗
       (▷ P -∗ closeInv N P -∗
        ∃ v',
        ▷ l ↦{q} v' ∗
        ▷ (l ↦{q} v' -∗ (REL fill K (of_val v') ≤ e2 @ (⊤ ∖ ↑N) <|X|> {{R}}))) -∗
       REL fill K (! #l) ≤ e2 <|X|> {{R}}.
     Proof.
       iIntros "Hinv Hrel".
       iApply (rel_load_l_inv' _ (⊤ ∖ ↑N)).
       iMod (inv_acc with "Hinv") as "[HP Hclose]"; auto.
       iModIntro.
       iDestruct ("Hrel" with "HP Hclose") as "[%v' [Hl Hrel]]".
       iExists v'. by iFrame.
     Qed. *)

  (* Lemma rel_load_r_with_mask E X R e1 k2 l2 dq2 v2 :
       ↑specN ⊆ E →
       l2 ↦ₛ{dq2} v2 -∗
       (l2 ↦ₛ{dq2} v2 -∗ REL e1 ≤ fill k2 v2 @ E <|X|> {{R}}) -∗
       REL e1 ≤ fill k2 (! #l2) @ E <|X|> {{R}}.
     Proof.
       rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
       iIntros (HE) "Hl2 Hrel %k1' %k2' %S Hkwp %j %k2'' #Hspec Hj".
       rewrite -!fill_app.
       iMod (step_load with "Hspec Hj Hl2") as "[Hj Hl2]"; first done.
       rewrite !fill_app.
       iApply ("Hrel" with "Hl2 Hkwp Hspec Hj").
     Qed. *)

  Lemma rel_load_r X R e1 k2 l2 dq2 v2 :
    l2 ↦ₛ{dq2} v2 -∗
    (l2 ↦ₛ{dq2} v2 -∗ REL e1 ≤ fill k2 v2 <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (! #l2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl2 Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    rewrite -!fill_app.
    iModIntro.
    iMod (step_load with "[Hj Hl2]") as "[Hj Hl2]"; first iFrame.
    rewrite !fill_app.
    iApply fupd_wp.
    iApply ("Hrel" with "Hl2 Hkwp Hj").
  Qed.

  Lemma rel_store_l X R k1 l1 v1 w1 e2 :
    ▷ l1 ↦ v1 -∗
    ▷ (l1 ↦ w1 -∗ REL fill k1 #(()%V) ≤ e2 <|X|> {{R}}) -∗
    REL fill k1 (#l1 <- w1) ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl1 Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    iEval (rewrite -fill_app).
    iModIntro.
    iApply wp_bind.
    iApply (wp_store with "Hl1").
    iIntros "!> Hl1". rewrite fill_app.
    iApply fupd_wp.
    iApply ("Hrel" with "Hl1 Hkwp Hj").
  Qed.

  (* Lemma rel_store_r_with_mask E X R e1 k2 l2 v2 w2 :
       nclose specN ⊆ E →
       l2 ↦ₛ v2 -∗
       (l2 ↦ₛ w2 -∗ REL e1 ≤ fill k2 #() @ E <|X|> {{R}}) -∗
       REL e1 ≤ fill k2 (#l2 <- w2) @ E <|X|> {{R}}.
     Proof.
       rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
       iIntros (HE) "Hl2 Hrel %k1' %k2' %S Hkwp %j %k2'' #Hspec Hj".
       rewrite -!fill_app.
       iMod (step_store with "Hspec Hj Hl2") as "[Hj Hl2]"; first done.
       rewrite !fill_app.
       iApply ("Hrel" with "Hl2 Hkwp Hspec Hj").
     Qed. *)

  Lemma rel_store_r X R e1 k2 l2 v2 w2 :
    l2 ↦ₛ v2 -∗
    (l2 ↦ₛ w2 -∗ REL e1 ≤ fill k2 #(()%V) <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (#l2 <- w2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl2 Hrel %k1' %k2' %S Hkwp %k2'' Hj".
    rewrite -!fill_app. iModIntro.
    iMod (step_store with "[$Hj $Hl2]") as "[Hj Hl2]".
    rewrite !fill_app.
    iApply fupd_wp.
    iApply ("Hrel" with "Hl2 Hkwp Hj").
  Qed.

End baze_rules.

(* ========================================================================= *)
(* blaze: A Logic for Dynamic Labels. *)

(* ------------------------------------------------------------------------- *)
(* Model. *)

Section brel.
  Context `{!probblazeGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (* Collect labels [labels_(l/r)]. *)

  Definition labels_l (L : iLblThy Σ) : list label :=
    concat L.*1.*1.

  Definition labels_r (L : iLblThy Σ) : list label :=
    concat L.*1.*2.

  (* ----------------------------------------------------------------------- *)
  (* Label-validity predicate. *)

  Definition valid_l (L : iLblThy Σ) : iProp Σ :=
    let l1s := labels_l L in
    [∗ list] l1 ∈ l1s, is_label l1 DfracDiscarded.

  Definition valid_r (L : iLblThy Σ) : iProp Σ :=
    let l2s := labels_r L in
    [∗ list] l2 ∈ l2s, spec_labels_frag l2 DfracDiscarded.

  Definition valid (L : iLblThy Σ) : iProp Σ :=
    valid_l L ∗ valid_r L.

  (* ----------------------------------------------------------------------- *)
  (* Distinct predicate. *)

  Definition distinct_l (L : iLblThy Σ) : Prop :=
    NoDup (labels_l L).

  Definition distinct_r (L : iLblThy Σ) : Prop :=
    NoDup (labels_r L).

  Definition distinct (L : iLblThy Σ) : Prop :=
    distinct_l L ∧ distinct_r L.

  Definition distinct' (L : iLblThy Σ) : iProp Σ :=
    ⌜ distinct L ⌝.

  (* ----------------------------------------------------------------------- *)
  (* Refinement relation in blaze. *)

  Definition brel :
    expr -d> expr -d> iLblThy Σ -d> (val -d> val -d> iProp Σ) -d> iProp Σ
  := (λ e1 e2 L R,
    valid L -∗ distinct' L -∗ REL e1 ≤ e2 <|to_iThy L|> {{R}}
  )%I.


  
