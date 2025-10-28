From iris.prelude Require Import options.

From iris.algebra Require Import list.
From iris.proofmode  Require Export base tactics classes proofmode.
From iris.base_logic Require Import na_invariants.

From clutch.common Require Import locations.
From clutch.approxis Require Export app_weakestpre coupling_rules.

From clutch.prelude Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Export spec_rules class_instances primitive_laws metatheory coupling_rules.
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

Class probblazeRGS Σ := ProbblazeRGS {
                        probblazeRGS_probblazeGS :: probblazeGS Σ;
                        probblazeRGS_na_invG :: na_invG Σ;
                        probblazeRGS_nais : na_inv_pool_name;
                      }.

Definition na_ownP `{!probblazeRGS Σ} := na_own probblazeRGS_nais.
Definition na_invP `{!probblazeRGS Σ} := na_inv probblazeRGS_nais.
Definition na_closeP `{!probblazeRGS Σ} P N E := (▷ P ∗ na_ownP (E ∖ ↑N) ={⊤}=∗ na_ownP E)%I.

Section rel.
  Context `{!probblazeRGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (* Observational refinement. *)

  
 

  Definition obs_refines_def :
    coPset -d> expr -d> expr -d> (val -d> val -d> iProp Σ) -d> iProp Σ := 
    (λ E e1 e2 R, ∀ k ε,
        ⤇ fill k e2 -∗
        na_ownP E -∗
        ↯ ε -∗
        ⌜ (0 < ε)%R ⌝ -∗
        WP e1 {{ v1, ∃ (v2 : val) ε, ⤇ fill k (of_val v2) ∗ 
                                   R v1 v2 ∗ 
                                   na_ownP ⊤ ∗ 
                                   ↯ ε ∗ 
                                   ⌜ (0 < ε)%R ⌝ }})%I.
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
  Context `{!probblazeRGS Σ}.

  Implicit Types X Y Z : iThy Σ.

  Lemma obs_refines_value (v1 v2 : val) R : R v1 v2 -∗ obs_refines ⊤ v1 v2 R.
  Proof.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros "HR" (k ε) "Hj Hna Herr %Hpos".
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
  
  (* Lemma fupd_obs_refines E1 E2 e1 e2 R :
       (|={E1, E2}=> obs_refines E2 e1 e2 R) ⊢ obs_refines E1 e1 e2 R.
     Proof.
       rewrite obs_refines_eq /obs_refines_def.
       iIntros "H" (k) "Hj". iMod "H" as "H".
       by iApply ("H" with "Hj").
     Qed. *)


  Lemma fupd_obs_refines E e1 e2 R :
    (|={⊤}=> obs_refines E e1 e2 R) ⊢ obs_refines E e1 e2 R.
  Proof.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros "H". iIntros (K ε) "HK /=".
    iMod "H" as "H". iApply ("H" with "HK").
  Qed.


  Global Instance elim_fupd_refines p E e t P A :
   ElimModal True p false (|={⊤}=> P) P
     (obs_refines E e t A) (obs_refines E e t A).
  Proof.
    rewrite /ElimModal. intros _.
    iIntros "[HP HI]". iApply fupd_obs_refines.
    destruct p; simpl; rewrite ?bi.intuitionistically_elim;
    iMod "HP"; iModIntro; by iApply "HI".
  Qed.

  Global Instance elim_bupd_logrel p E e t P A :
    ElimModal True p false (|==> P) P
      (obs_refines E e t A) (obs_refines E e t A).
  Proof.
    rewrite /ElimModal (bupd_fupd ⊤). apply: elim_fupd_refines.
  Qed.
    
  (* Lemma fupd_rel' E1 E2 e1 e2 X R :
       (|={E1, E2}=> REL e1 ≤ e2 @ E2 <|X|> {{R}}) ⊢ REL e1 ≤ e2 @ E1 <|X|> {{R}}.
     Proof.
       rewrite !rel_unfold /rel_pre.
       iIntros "Hrel" (k1 k2 S) "Hkwp".
       rewrite obs_refines_eq /obs_refines_def.
       iIntros (k) "Hj".
       iMod "Hrel" as "Hrel".
       by iSpecialize ("Hrel" with "Hkwp Hj").
     Qed. *)

  Lemma fupd_rel e1 e2 E X R : (|={⊤}=> REL e1 ≤ e2 @ E <|X|> {{R}}) ⊢ REL e1 ≤ e2 @ E <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros "Hrel" (k1 k2 S) "Hkwp".
    iApply fupd_obs_refines. iMod "Hrel".
    iModIntro.
    by iApply "Hrel".
  Qed.
    
  (* This is useful for stripping off laters of timeless propositions. *)
  Global Instance is_except_0_logrel E e t X R :
    IsExcept0 (rel E e t X R).
  Proof.
    rewrite /IsExcept0. iIntros "HL".
    iApply fupd_rel. by iMod "HL".
  Qed.

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

  (* from approxis *)
  Lemma rel_atomic_l (E E' : coPset) K e1 t X R
    (Hatomic : Atomic StronglyAtomic e1) :
    (∀ K', ⤇ fill K' t ={⊤, E'}=∗
             WP e1 @ E' {{ v,
              |={E', ⊤}=> ∃ t', ⤇ fill K' t' ∗
              REL fill K (of_val v) ≤ t' @ E <| X |> {{R}} }})%I
   ⊢ REL fill K e1 ≤ t @ E <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros "Hlog".
    iIntros (k1 k2 S) "Hkwp".
    iIntros (k ε) "Hj Hnais Herr %Hpos /=".
    rewrite -!fill_app.
    iApply wp_bind. iApply wp_atomic; auto.
    iMod ("Hlog" with "Hj") as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    iMod "Hlog" as (t') "[Hr Hlog]".
    rewrite !rel_unfold /rel_pre.
    rewrite obs_refines_eq /obs_refines_def.
    rewrite !fill_app. 
    iSpecialize ("Hlog" with "Hkwp Hr Hnais Herr").
    by iApply "Hlog".
  Qed.

  (* Lemma rel_atomic_l (E : coPset) K e1 e2 X R
           (Hatomic : Atomic StronglyAtomic e1) :
      (|={⊤,E}=> WP e1 @ E {{ v,
        REL fill K (of_val v) ≤ e2 @ E <|X|> {{R}} }})%I -∗
      REL fill K e1 ≤ e2 <|X|> {{R}}.
     Proof.
       rewrite !rel_unfold /rel_pre.
       rewrite obs_refines_eq /obs_refines_def.
       iIntros "Hlog".
       iIntros (k1 k2 S) "Hkwp".
       iIntros (k) "Hj /=". (* iModIntro. *)
       rewrite -!fill_app.
       iApply wp_bind. iApply wp_atomic; auto.
       iMod "Hlog" as "He". iModIntro.
       iApply (wp_wand with "He").
       iIntros (v) "Hlog".
       rewrite !rel_unfold /rel_pre.
       rewrite obs_refines_eq /obs_refines_def.
       rewrite !fill_app. 
       by iSpecialize ("Hlog" with "Hkwp Hj").
     Qed. *)



  Lemma rel_inv_close E N P e1 e2 X R :
   ⊢ na_closeP P N E -∗
      ▷ P -∗
      REL e1 ≤ e2 @ E <|X|> {{R}} -∗
      REL e1 ≤ e2 @ (E ∖ ↑N) <|X|> {{R}}.
  Proof.
    iIntros "Hclose HP Hrel".
    rewrite !rel_unfold /rel_pre.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp".
    iIntros (k ε) "Hj Hnais Herr %Hpos /=".
    iDestruct ("Hclose" with "[$HP $Hnais]") as "own_F".
    iMod "own_F".
    by iApply ("Hrel" with "Hkwp Hj own_F Herr").  
  Qed.
    
  (*
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
     Qed. *)

  Lemma rel_inv_alloc N P e1 e2 X R :
   ▷ P -∗
   (inv N P -∗ REL e1 ≤ e2 <|X|> {{R}}) -∗
   REL e1 ≤ e2 <|X|> {{R}}.
  Proof.
    iIntros "HP Hrel".
    iApply fupd_rel.
    iMod (inv_alloc N ⊤ P with "HP") as "Hinv".
    iModIntro.
    by iApply "Hrel".
  Qed.
  
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

  Lemma rel_exhaustion_sum_r k1 k2 e1 e2 X Y Z R S :
    traversable k1 k2 Y -∗

    REL e1 ≤ e2 <|iThySum X Y|> {{R}} -∗

    □ (
      (∀ v1 v2, R v1 v2 -∗ REL fill k1 v1 ≤ fill k2 v2 <|iThySum Z Y|> {{S}})

        ∧

      (∀ e1' e2' Q,
        X e1' e2' Q -∗
        □ ▷ (∀ s1 s2, Q s1 s2 -∗ REL s1 ≤ s2 <|iThySum X Y|> {{R}}) -∗
        REL fill k1 e1' ≤ fill k2 e2' <|iThySum Z Y|> {{S}})
    ) -∗

    REL fill k1 e1 ≤ fill k2 e2 <|iThySum Z Y|> {{S}}.
  Proof.
    iIntros "#Htraversable He12 Hfill".
    iApply (rel_introduction_mono with "[He12 Hfill]"); last iApply iThy_le_sum_swap.
    iApply (rel_exhaustion_sum_l with "Htraversable [He12] [Hfill]").
    { iApply (rel_introduction_mono with "He12").
      by iApply iThy_le_sum_swap.
    }
    { iDestruct "Hfill" as "#Hfill"; iModIntro; iSplit.
      - iIntros (v1 v2) "HR".
        iApply (rel_introduction_mono with "[HR Hfill]"); last iApply iThy_le_sum_swap.
        by iApply "Hfill".
      - iIntros (e1' e2' Q) "HX #Hk".
        iApply (rel_introduction_mono with "[HX Hfill Hk]"); last iApply iThy_le_sum_swap.
        iApply ("Hfill" with "HX").
        iIntros "!> !>" (s1 s2) "HQ".
        iSpecialize ("Hk" with "HQ").
        iApply (rel_introduction_mono with "Hk").
        by iApply iThy_le_sum_swap.
    }
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
    iIntros (Hφ Hexec) "He1' %k2 %ε Hj Hna Herr %Hpos".
    iApply wp_pure_step_later; [done|].
    iIntros "!>".
    by iApply ("He1'" with "Hj Hna Herr").
  Qed.
 
  Lemma obs_refines_pure_step_r_with_mask E e1 e2 e2' φ n S :
    φ →
    PureExec φ n e2 e2' →
    obs_refines E e1 e2' S -∗ obs_refines E e1 e2 S.
  Proof.
    rewrite obs_refines_eq /obs_refines_def.
    iIntros (Hφ Hexec) "He1' %k2 %ε Hj Hnais Herr %Hpos". 
    iMod (step_pure with "Hj") as "Hj"; first done.
    by iApply ("He1'" with "Hj Hnais Herr"). 
  Qed.

  Lemma obs_refines_pure_step_r e1 e2 e2' φ n S :
    φ →
    PureExec φ n e2 e2' →
    obs_refines ⊤ e1 e2' S -∗ obs_refines ⊤ e1 e2 S.
  Proof. by apply obs_refines_pure_step_r_with_mask. Qed.

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

  Lemma rel_pure_step_r_with_mask E e1 e2 e2' φ n X R :
    PureExec φ n e2 e2' →
    φ →
    REL e1 ≤ e2' @ E <|X|> {{R}} ⊢ REL e1 ≤ e2 @ E <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre.
    iIntros (Hexec Hφ) "Hrel"; iIntros (k1 k2 S) "Hkwp".
    iApply (obs_refines_pure_step_r_with_mask _ _ (fill k2 e2) (fill k2 e2')).
    { by apply Hφ. }
    { by apply pure_exec_ctx. }
    { by iApply "Hrel". }
  Qed.

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

  Lemma rel_effect_l X k1 s1 e1 e2 R :
    ▷ (∀ l1, primitive_laws.is_label l1 (DfracOwn 1) ==∗ REL fill k1 (lbl_subst s1 l1 e1) ≤ e2 <|X|> {{R}}) -∗
    REL fill k1 (Effect s1 e1) ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel" (k1' k2' S) "Hkwp %k2 %ε Hj Hnais Herr %Hpos".
    rewrite -(fill_app k1'). 
    iApply wp_effect. 
    iIntros "!> %l1 Hl1".
    iMod ("Hrel" with "Hl1") as "Hrel".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    rewrite fill_app.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_effect_r X R e1 k2 s2 e2 :
    (∀ l2, spec_labels_frag l2 (DfracOwn 1) ==∗ REL e1 ≤ fill k2 (lbl_subst s2 l2 e2) <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (Effect s2 e2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app. 
    iMod (step_alloc_label with "Hj") as (l) "[Hj Hl]".
    rewrite !fill_app.
    iMod ("Hrel" with "Hl") as "Hrel".
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
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
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    iEval (rewrite -fill_app).
    iApply wp_bind.
    iApply wp_alloc; first done.
    iIntros "!> %l1 Hpoints_to".
    iSpecialize ("Hrel" with "Hpoints_to").
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq fill_app.
    iApply fupd_wp.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_alloc_r X R e1 k2 v2 :
    (∀ l2, l2 ↦ₛ v2 -∗ REL e1 ≤ fill k2 #l2 <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (ref v2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iMod (step_alloc with "Hj") as (l2) "[Hj Hl2]".
    iSpecialize ("Hrel" with "Hl2").
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq !fill_app.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_load_l X R k1 l1 dq1 v1 e2 :
    ▷ l1 ↦{dq1} v1 -∗
    ▷ (l1 ↦{dq1} v1 -∗ REL fill k1 v1 ≤ e2 <|X|> {{R}}) -∗
    REL fill k1 (! #l1) ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl1 Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    iEval (rewrite -fill_app).
    iApply wp_bind.
    iApply (wp_load with "Hl1").
    iIntros "!> Hl1". rewrite fill_app.
    by iApply ("Hrel" with "Hl1 Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_load_l_mask K E l q e2 X R :
    (∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') ≤ e2 @ E <|X|> {{R}})))%I
    ⊢ REL fill K (! #l) ≤ e2 @ E <|X|> {{R}}.
  Proof.
    iIntros "Hrel".
    iApply (rel_atomic_l). iDestruct "Hrel" as "[%v [Hl Hrel]]". 
    iIntros (K') "Hj". 
    iApply (wp_load with "Hl"). iModIntro. iNext. iIntros "Hl !>".  iFrame.
    by iApply "Hrel".
  Qed.

  (* Lemma rel_load_l_inv N P K l q e2 X R :
       inv N P -∗
       (▷ P -∗ na_closeP P N ⊤ -∗
        ∃ v',
        ▷ l ↦{q} v' ∗
        ▷ (l ↦{q} v' -∗ (REL fill K (of_val v') ≤ e2 @ (⊤ ∖ ↑N) <|X|> {{R}}))) -∗
       REL fill K (! #l) ≤ e2 <|X|> {{R}}.
     Proof.
       iIntros "Hinv Hrel".
       iApply rel_load_l_mask.
       iMod (inv_acc with "Hinv") as "[HP Hclose]"; auto.
       iModIntro.
       iDestruct ("Hrel" with "HP Hclose") as "[%v' [Hl Hrel]]".
       iExists v'. by iFrame.
     Qed. *)

  Lemma rel_load_r_with_mask E X R e1 k2 l2 dq2 v2 :
    l2 ↦ₛ{dq2} v2 -∗
    (l2 ↦ₛ{dq2} v2 -∗ REL e1 ≤ fill k2 v2 @ E <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (! #l2) @ E <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl2 Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app. 
    iMod (step_load with "[Hj Hl2]") as "[Hj Hl2]"; first iFrame.
    rewrite !fill_app.
    by iApply ("Hrel" with "Hl2 Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_load_r X R e1 k2 l2 dq2 v2 :
    l2 ↦ₛ{dq2} v2 -∗
    (l2 ↦ₛ{dq2} v2 -∗ REL e1 ≤ fill k2 v2 <|X|> {{R}}) -∗
    REL e1 ≤ fill k2 (! #l2) <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl2 Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iMod (step_load with "[Hj Hl2]") as "[Hj Hl2]"; first iFrame.
    rewrite !fill_app.
    iApply fupd_wp.
    by iApply ("Hrel" with "Hl2 Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_store_l X R k1 l1 v1 w1 e2 :
    ▷ l1 ↦ v1 -∗
    ▷ (l1 ↦ w1 -∗ REL fill k1 #(()%V) ≤ e2 <|X|> {{R}}) -∗
    REL fill k1 (#l1 <- w1) ≤ e2 <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hl1 Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    iEval (rewrite -fill_app).
    iApply wp_bind.
    iApply (wp_store with "Hl1").
    iIntros "!> Hl1". rewrite fill_app.
    by iApply ("Hrel" with "Hl1 Hkwp Hj Hnais Herr").
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
    iIntros "Hl2 Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app. 
    iMod (step_store with "[$Hj $Hl2]") as "[Hj Hl2]".
    rewrite !fill_app.
    by iApply ("Hrel" with "Hl2 Hkwp Hj Hnais Herr").
  Qed.

  (* Rel rules probabilistic fragment *)

  Lemma rel_alloctape_r E K N z t X R :
    TCEq N (Z.to_nat z) →
    (∀ α : loc, α ↪ₛ (N; []) -∗ REL t ≤ fill K (of_val #lbl:α) @ E <|X|> {{R}})%I
    ⊢ REL t ≤ fill K (alloc #z) @ E <|X|> {{R}}.
  Proof.
    iIntros (HE) "/=".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iMod (step_alloctape with "Hj") as (α) "[Hj Hα]".
    iSpecialize ("Hrel" $! α with "Hα").
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq !fill_app.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.    

  Lemma rel_alloctape_l K E N z t X R :
    TCEq N (Z.to_nat z) →
    (▷ (∀ α : loc, α ↪N (N; []) -∗ REL fill K (of_val #lbl:α) ≤ t @ E <|X|> {{R}}))%I
    ⊢ REL fill K (alloc #z) ≤ t @ E <|X|> {{R}}.
  Proof.
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (HE) "Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    iEval (rewrite -fill_app).
    iApply wp_bind.
    iApply wp_alloc_tape; [done|].
    iIntros "!> %α Hα". rewrite fill_app.
    iSpecialize ("Hrel" with "Hα").
    rewrite rel_unfold /rel_pre obs_refines_eq /obs_refines_eq.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.
  
  Lemma rel_couple_rand_rand N f `{Bij nat nat f} z K K' X R :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) →
    (∀ n : nat, REL fill K #(n) ≤ fill K' #(f n) <|X|> {{R}})
        ⊢ REL fill K (rand #z) ≤ fill K' (rand #z) <|X|> {{R}}.
  Proof.
    iIntros (??) "Hrel".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "%k1 %k2 %S Hkwp %k2' %ε Hj Hnais Herr %Hpos".
    do 3rewrite -fill_app.
    iApply wp_bind.
    iApply (wp_couple_rand_rand with "Hj"); [done|].
    iIntros "!> %n (%Hlt & Hj)".
    iSpecialize ("Hrel" $! n).
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    do 3rewrite fill_app.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.

  Lemma rel_randT_r K E α N z n ns t X R :
    TCEq N (Z.to_nat z) →
    α ↪ₛN (N; n :: ns)
   ⊢ (α ↪ₛN (N; ns)-∗ ⌜ n ≤ N ⌝ -∗ REL t ≤ fill K (of_val #n) @ E <|X|> {{R}})
    -∗ REL t ≤ (fill K (rand(#lbl:α) #z)) @ E <|X|> {{R}}.
  Proof.
    iIntros (HE) "Hα /=".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "Hrel %k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iMod (step_randnat with "[Hj Hα]") as "[Hj [%Hlt Hα]]"; first iFrame.
    iSpecialize ("Hrel" with "Hα").
    iSpecialize ("Hrel" $! Hlt).
    rewrite !fill_app.
    by iApply ("Hrel" with "Hkwp Hj Hnais Herr").
  Qed.     
  Definition rel_rand_r := rel_randT_r.

  Lemma rel_randT_empty_r K E α N z e X R :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛN (N; []) ∗
      (∀ n : nat, α ↪ₛN (N; []) -∗ ⌜ n ≤ N ⌝ -∗ REL e ≤ fill K (Val #n) @ E <|X|> {{R}})
    ⊢ REL e ≤ fill K (rand(#lbl:α) #z) @ E <|X|> {{R}}.
  Proof.
    iIntros (->) "[>Hα H]".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "%k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iApply wp_rand_empty_r.
    iFrame "Hα Hj".
    iIntros (N) "(Hα & Hj) %Hlt".
    rewrite /= fill_app.
    iSpecialize ("H" with "Hα").
    iSpecialize ("H" $! (INR_le _ _ Hlt)).
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    rewrite !fill_app.
    by iApply ("H" with "Hkwp Hj Hnais Herr").
  Qed.    
  Definition rel_rand_empty_r := rel_randT_empty_r.

  Lemma rel_randU_empty_r K E N z e X R :
    TCEq N (Z.to_nat z) →
    (∀ n, ⌜ n ≤ N ⌝ -∗ REL e ≤ fill K (Val #n) @ E <|X|> {{R}}) -∗
    REL e ≤ fill K (rand #z) @ E <|X|> {{R}}.
  Proof.
    iIntros (->) "H".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp %k2' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iApply wp_rand_r. iFrame.
    iIntros (n) "Hj %Hlt".
    apply INR_le in Hlt.
    iSpecialize ("H" $! n Hlt).
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    rewrite !fill_app.
    by iApply ("H" with "[$][$][$][$]").
  Qed.
  
  Lemma rel_randT_l E K α N z n ns t X R :
    TCEq N (Z.to_nat z) →
    (▷ α ↪N (N; n :: ns) ∗
     ▷ (α ↪N (N; ns) -∗ ⌜ n ≤ N ⌝ -∗ REL fill K (of_val #n) ≤ t @ E <|X|> {{R}}))
    ⊢ REL fill K (rand(#lbl:α) #z) ≤ t @ E <|X|> {{R}}.
  Proof.
    iIntros (->) "[>Hα Hlog]".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "%k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iApply wp_bind.
    iApply (wp_rand_tape with "Hα").
    iIntros "!> (Hα & %Hlt)".
    rewrite !fill_app.
    iApply ("Hlog" with "[$][][$][$][$][$]"); eauto using INR_le.
  Qed.
  Definition rel_rand_l := rel_randT_l.

  Lemma rel_randT_empty_l K E α N z e X R :
    TCEq N (Z.to_nat z) →
    ▷ α ↪N (N; []) ∗
    ▷ (∀ (n : nat), α ↪N (N; []) -∗ ⌜ n ≤ N ⌝ -∗ REL fill K (Val #n) ≤ e @ E <|X|> {{R}})
    ⊢ REL fill K (rand(#lbl:α) #z) ≤ e @ E <|X|> {{R}}.
  Proof.
    iIntros (->) "[>Hα H]".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros "%k1' %k2' %S Hkwp %k2'' %ε Hj Hnais Herr %Hpos".
    rewrite -!fill_app.
    iApply wp_bind.
    iApply (wp_rand_tape_empty with "Hα").
    iIntros (n) "!> (Hα & %Hlt)". 
    rewrite !fill_app.
    iSpecialize ("H" $! n with "Hα").
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iApply ("H" with "[][$][$][$][$]"); eauto using INR_le.
  Qed.
  Definition rel_rand_empty_l := rel_randT_empty_l.

  Lemma rel_randU_empty_l K E N z e X R :
    TCEq N (Z.to_nat z) →
    (∀ n, ⌜ n ≤ N ⌝ -∗ REL fill K (Val #n) ≤ e@ E <|X|> {{R}}) -∗
    REL fill K (rand #z) ≤ e @ E <|X|> {{R}}.
  Proof.
    iIntros (->) "H".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp %k' %ε Hj Hnais Herr Hlt".
    rewrite -!fill_app.
    iApply wp_bind.
    iApply wp_rand; first done; simpl.
    iIntros (n Hlt%INR_le) "!>".
    iSpecialize ("H" $! n Hlt).
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    rewrite !fill_app.
    iApply ("H" with "[$][$][$][$][$]").
  Qed.
    
  Lemma rel_couple_couple_avoid (N:nat) l z E K K' X R:
    NoDup l ->
    TCEq N (Z.to_nat z) →
    ↯ (length l / (S N)) ∗
    ▷ (∀ (n : fin (S N)), ⌜n ∉ l⌝ -∗ REL fill K (Val #n) ≤ fill K' (Val #n) @ E <|X|> {{R}})
    ⊢ REL fill K (rand #z) ≤ fill K' (rand #z) @ E <|X|> {{R}}.
  Proof.
    iIntros (Hl ->) "[Hε HΦ]".
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp %k %ε Hfill Hown Herr %Hpos".
    rewrite -!fill_app.
    iApply wp_bind.
    (* rewrite -fill_app. *)
    rewrite S_INR.
    iApply (wp_couple_rand_rand_avoid with "[$]"); first done.
    iIntros "!>" (n) "[% Hspec]".
    rewrite !fill_app.
    iSpecialize ("HΦ" $! n H).
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    by iApply ("HΦ" with "[$][$][$][$]").
  Qed.
    
  Lemma rel_couple_TT_frag (N M : nat) (f : nat -> nat) {_ : Inj (=) (=) f} E e1 e2 X R α αₛ ns nsₛ :
    (M <= N)%nat →
    (∀ n : nat, n < S M → f n < S N)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (n : nat),
        ⌜ n ≤ N ⌝ -∗
        if bool_decide (∃ m, m ≤ M /\ f m = n) then
          ∀ m, α ↪N (N; ns ++ [f m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜f m ≤ N⌝ ∗ ⌜m ≤ M⌝ -∗
               REL e1 ≤ e2 @ E <|X|> {{R}}
        else
          α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗ REL e1 ≤ e2 @ E <|X|> {{R}}
    )
    ⊢ REL e1 ≤ e2 @ E <|X|> {{R}}.
  Proof.
    iIntros (Hleq Hdom) "(Hα & Hαs & Hlog)". 
    rewrite {3}(rel_unfold E e1 e2 X R) /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp %K2 %ε' He2 Hnais Herr' Hpos/=".
    iApply wp_couple_fragmented_rand_rand_inj; [done|done|].
    iFrame.
    iIntros (n) "%".
    iSpecialize ("Hlog" $! n).
    case_bool_decide.
    - iIntros (m) "(Hα & Hαs & Hnm)".
      iSpecialize ("Hlog" $! H0 m with "[$]").
      rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
      iApply ("Hlog" with "Hkwp He2 Hnais Herr' Hpos").
    - iIntros "(Hα & Hαs)".
      iSpecialize ("Hlog" $! H0  with "[$]").
      rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
      iApply ("Hlog" with "Hkwp He2 Hnais Herr' Hpos").
  Qed.

  Lemma rel_couple_TT_adv (N M : nat) (f : nat → nat) {_ : Inj (=) (=) f} E e1 e2 X A α αₛ ns nsₛ (ε : R) :
    (0 <= ε)%R →
    (N < M)%nat →
    (∀ n : nat, n < S N → f n < S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗
    (∀ (m : nat),
        ⌜ m ≤ M ⌝ -∗
        if bool_decide (∃ n, n ≤ N /\ f n = m) then
          ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜n ≤ N⌝ ∗ ⌜f n ≤ M⌝ -∗
               REL e1 ≤ e2 @ E <|X|> {{A}}
        else
          ∀ (ε' : R),
            ⌜ε' = ((S M) / (S M - S N) * ε)%R⌝ ∗
            α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗
            REL e1 ≤ e2 @ E <|X|> {{A}})
    ⊢ REL e1 ≤ e2 @ E <|X|> {{A}}.
  Proof.
    iIntros (Hε Hleq Hdom) "(Hα & Hαs & Herr & Hlog)".
    rewrite {3}(rel_unfold E e1 e2 X A) /rel_pre obs_refines_eq /obs_refines_def.
    set ε' := mknonnegreal _ Hε.
    replace ε with ε'.(nonneg); [|done]. 
    iIntros (k1 k2 S) "Hkwp %K2 %ε2 He2 Hnais Herr' %Hε'".
    iApply (wp_couple_fragmented_rand_rand_inj_rev' _ _ _ _ _ _ _ _ ε') ; [done|done|done| ].
    iFrame "Hα Hαs Herr".
    iIntros (m) "%".
    iSpecialize ("Hlog" $! m).
    case_bool_decide.
    - iIntros (n) "(Hα & Hαs & Hnm & Hfnm)".
      iSpecialize ("Hlog" $! H0 n with "[$]").
      rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
      by iApply ("Hlog" with "Hkwp He2 Hnais Herr'").
    - iIntros (ε'0) "(%Herr2 & Hα & Hαs & Herr'0 & %Hnm)".
      iSpecialize ("Hlog" $! H0 ε'0).
      rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
      iApply ("Hlog" with "[$Hα $Hαs $Herr'0 //][$][$][$][$][//]").
  Qed.

  (* Error credit amplification *)
  Lemma rel_get_ec E e e' X A :
    (∀ ε : R, (↯ ε) -∗ ⌜(0 < ε)%R⌝ -∗ REL e ≤ e' @ E <|X|> {{A}}) ⊢
    (REL e ≤ e' @ E <|X|> {{A}}).
  Proof.
    iIntros "H".
    rewrite {2} (rel_unfold E e e' X A).
    rewrite /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp".
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    replace (ε) with (ε / 2 + ε / 2)%R by lra. 
    iDestruct (ec_split with "Herr") as "[Herr1 Herr2]";
      [lra|lra|].
    iSpecialize ("H" $! (ε / 2) with "Herr1").
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iApply ("H" with "[][$][$][$][$][]"); iPureIntro; lra.
  Qed.

  Lemma rel_ind_amp E e e' X A (k : R) :
    (1 < k)%R ->
    □ (∀ (ε : R),
          ⌜(0 < ε)%R⌝ -∗ □(↯ (k * ε) -∗ (REL e ≤ e' @ E <|X|> {{A}}))
                         -∗ ↯ ε -∗ (REL e ≤ e' @ E <|X|> {{A}}))%I
    ⊢ REL e ≤ e' @ E <|X|> {{A}}.
  Proof.
    intros Hk.
    iIntros "#IH".
    iApply rel_get_ec.
    iIntros (ε) "Herr %Hpos".
    iApply (ec_ind_amp _ k with "[IH] Herr"); auto.
  Qed.
  
End baze_rules.

(* ========================================================================= *)
(* blaze: A Logic for Dynamic Labels. *)

(* ------------------------------------------------------------------------- *)
(* Model. *)

Section brel.
  Context `{!probblazeRGS Σ}.

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

  (* ----------------------------------------------------------------------- *)
  (* Non-expansiveness proofs. *)

  (* labels_l. *)
  Global Instance labels_l_ne n : Proper (dist n ==> (=)) labels_l.
  Proof.
    intros x y H. rewrite /labels_l.
    apply (list_fmap_ne _ fst fst) in H; last solve_proper.
    apply (list_fmap_ne _ fst fst) in H; last solve_proper.
    apply discrete in H; last tc_solve.
    f_equiv. by apply leibniz_equiv.
  Qed.
  Global Instance labels_l_proper : Proper ((≡) ==> (=)) labels_l.
  Proof. intros ???. by apply (labels_l_ne 0), equiv_dist. Qed.

  (* labels_r. *)
  Global Instance labels_r_ne n : Proper (dist n ==> (=)) labels_r.
  Proof.
    intros x y H. rewrite /labels_r.
    apply (list_fmap_ne _ fst fst) in H; last solve_proper.
    apply (list_fmap_ne _ snd snd) in H; last solve_proper.
    apply discrete in H; last tc_solve.
    f_equiv. by apply leibniz_equiv.
  Qed.
  Global Instance labels_r_proper : Proper ((≡) ==> (=)) labels_r.
  Proof. intros ???. by apply (labels_r_ne 0), equiv_dist. Qed.

  (* valid_l. *)
  Global Instance valid_l_ne n : Proper (dist n ==> (≡)) valid_l.
  Proof. intros ?? H. rewrite /valid_l. by rewrite H. Qed.
  Global Instance valid_l_proper : Proper ((≡) ==> (≡)) valid_l.
  Proof. intros ???. by apply (valid_l_ne 0), equiv_dist. Qed.

  (* valid_r. *)
  Global Instance valid_r_ne n : Proper (dist n ==> (≡)) valid_r.
  Proof. intros ?? H. rewrite /valid_r. by rewrite H. Qed.
  Global Instance valid_r_proper : Proper ((≡) ==> (≡)) valid_r.
  Proof. intros ???. by apply (valid_r_ne 0), equiv_dist. Qed.

  (* valid. *)
  Global Instance valid_ne : NonExpansive valid.
  Proof. intros n ?? H. by rewrite /valid H. Qed.
  Global Instance valid_proper : Proper ((≡) ==> (≡)) valid.
  Proof. apply: ne_proper. Qed.

  (* distinct_l. *)
  Global Instance distinct_l_ne n : Proper (dist n ==> (↔)) distinct_l.
  Proof. intros ?? H. by rewrite /distinct_l H. Qed.
  Global Instance distinct_l_proper : Proper ((≡) ==> (↔)) distinct_l.
  Proof. intros ???. by apply (distinct_l_ne 0), equiv_dist. Qed.

  (* distinct_r. *)
  Global Instance distinct_r_ne n : Proper (dist n ==> (↔)) distinct_r.
  Proof. intros ?? H. by rewrite /distinct_r H. Qed.
  Global Instance distinct_r_proper : Proper ((≡) ==> (↔)) distinct_r.
  Proof. intros ???. by apply (distinct_r_ne 0), equiv_dist. Qed.

  (* distinct. *)
  Global Instance distinct_ne n : Proper (dist n ==> (↔)) distinct.
  Proof. intros ?? H. by rewrite /distinct H. Qed.
  Global Instance distinct_proper : Proper ((≡) ==> (↔)) distinct.
  Proof. intros ???. by apply (distinct_ne 0), equiv_dist. Qed.

  (* distinct'. *)
  Global Instance distinct'_ne : NonExpansive distinct'.
  Proof. intros n ?? H. by rewrite /distinct' H. Qed.
  Global Instance distinct'_proper : Proper ((≡) ==> (≡)) distinct'.
  Proof. apply: ne_proper. Qed.

  (* brel. *)
  Global Instance brel_ne e1 e2 : NonExpansive2 (brel e1 e2).
  Proof. by intros n ?? H ?? H'; rewrite /brel H H'. Qed.
  Global Instance brel_proper e1 e2 : Proper ((≡) ==> (≡) ==> (≡)) (brel e1 e2).
  Proof. apply: ne_proper_2. Qed.
End brel.

(* ------------------------------------------------------------------------- *)
(* Notation. *)

Notation "'BREL' e1 ≤ e2 <| L | > {{ R } }" :=
  (brel e1%E e2%E L%I R%I)
  (at level 20, e1, e2, L, R at next level, only parsing) : bi_scope.
(* Notation "'BREL' e1 ≤ e2  <| L | > {{ v1 ; v2 , Q } }" :=
     (brel e1%E e2%E L%I (λ v1 v2, Q)%I)
     (at level 20, e1, e2, L, Q at next level,
     format "'[hv' 'BREL'  e1  ≤  e2  '/' <| L | >  '/' {{  '[' v1  ;  v2 ,  '/' Q  ']' } } ']'") : bi_scope. *)

(* ------------------------------------------------------------------------- *)
(* Properties of [to_iThy]. *)

Section to_iThy.
  Context `{!probblazeRGS Σ}.
  Implicit Types L : iLblThy Σ.
  Implicit Types X Y : iThy Σ.

  Lemma traversable_to_iThy_nil k1 k2 :
    ⊢ traversable k1 k2 (to_iThy ([] : iLblThy Σ)).
  Proof. by iIntros "!>" (???) "[% [% [% [% _]]]]"; set_solver. Qed.

  Lemma traversable_to_iThy_cons k1 k2 l1s l2s X (L : iLblThy Σ) :
    traversable k1 k2 (iThyTraverse l1s l2s X) -∗
    traversable k1 k2 (to_iThy L) -∗
    traversable k1 k2 (to_iThy ((l1s, l2s, X) :: L)).
  Proof. 
    iIntros "#HXtrav #HLtrav !>" (???).
    rewrite to_iThy_cons.
    iIntros "[HX|HL]".
    - iDestruct ("HXtrav" with "HX") as "[%Q' [HX #HQ]]".
      iExists Q'. rewrite to_iThy_cons. by iSplit; [iLeft|].
    - iDestruct ("HLtrav" with "HL") as "[%Q' [HL #HQ]]".
      iExists Q'. rewrite to_iThy_cons. by iSplit; [iRight|].
  Qed.

  Lemma traversable_to_iThy_singleton k1 k2 l1s l2s X :
    traversable k1 k2 (iThyTraverse l1s l2s X) -∗
    traversable k1 k2 (to_iThy [(l1s, l2s, X)]).
  Proof.
    iIntros "#H".
    by iApply traversable_to_iThy_cons; [|iApply traversable_to_iThy_nil].
  Qed.

  Lemma iThy_le_to_iThy_sum l1s l2s X (L : _ Σ) :
   ⊢ iThy_le (to_iThy ((l1s, l2s, X) :: L)) (iThySum (iThyTraverse l1s l2s X) (to_iThy L)).
  Proof.
    iIntros "!>" (???) "[%l1s' [%l2s' [%Y [%Hin HY]]]]".
    rewrite elem_of_cons in Hin.
    destruct Hin as [Heq|Hin]; [injection Heq as -> -> ->|]; [by iLeft|iRight].
    iExists l1s', l2s', Y. by iFrame.
  Qed.

  Lemma iThy_le_sum_to_iThy l1s l2s X (L : _ Σ) :
   ⊢ iThy_le (iThySum (iThyTraverse l1s l2s X) (to_iThy L)) (to_iThy ((l1s, l2s, X) :: L)).
  Proof.
    iIntros "!>" (???) "[HX|[%l1s' [%l2s' [%Y [%Hin HY]]]]]".
    - iExists l1s, l2s, X. iFrame. by rewrite elem_of_cons; auto.
    - iExists l1s', l2s', Y. iFrame. by rewrite elem_of_cons; auto.
  Qed.

  Lemma iThy_le_to_iThy_1 l1s l2s (L : _ Σ) :
    ⊢ iThy_le (to_iThy ((l1s, l2s, iThyBot) :: L)) (to_iThy L).
  Proof.
    iApply (iThy_le_trans _ (iThySum (iThyTraverse l1s l2s iThyBot) (to_iThy L))).
    { by iApply iThy_le_to_iThy_sum. }
    by iIntros "!> %%% [?|?]"; [rewrite iThyTraverse_bot|].
  Qed.

  Lemma iThy_le_to_iThy_2 l1s l2s X (L : _ Σ) :
    ⊢ iThy_le (to_iThy L) (to_iThy ((l1s, l2s, X) :: L)).
  Proof.
    iIntros (e1' e2' Q) "!> [%l1s' [%l2s' [%Y [%Hin HX]]]]".
    iExists l1s', l2s', Y; iFrame. iPureIntro.
    by rewrite elem_of_cons; right.
  Qed.

  Lemma iThy_le_to_iThy_app L1 L2 :
    ⊢ iThy_le (iThySum (to_iThy L1) (to_iThy L2)) (to_iThy (L1 ++ L2)).
  Proof.
    iIntros "!> %%% [HL|HL]";
    iDestruct "HL" as "[%l1s [%l2s [%X [%Hin HX]]]]";
    iExists l1s, l2s, X; iFrame; iPureIntro; set_solver.
  Qed.

  Lemma iThy_le_to_iThy_app_inv L1 L2 :
    ⊢ iThy_le (to_iThy (L1 ++ L2)) (iThySum (to_iThy L1) (to_iThy L2)).
  Proof.
    iIntros "!> %%% [%l1s [%l2s [%X [%Hin HX]]]]".
    rewrite elem_of_app in Hin; destruct Hin; [iLeft|iRight];
    iExists l1s, l2s, X; iFrame; iPureIntro; set_solver.
  Qed.

  Lemma iThy_le_to_iThy_perm L L' :
    L ≡ₚ L' → ⊢ iThy_le (to_iThy L) (to_iThy L').
  Proof.
    revert L'; induction L as [|((l1s, l2s), X) L IH]; intro L'.
    - intros ?. by apply iThy_le_to_iThy_nil.
    - intros Hperm.
      destruct (Permutation_cons_inv_l _ _ _ Hperm) as [L1 [L2 [-> Hperm']]].
      iApply iThy_le_trans; first iApply iThy_le_to_iThy_sum.
      iApply iThy_le_trans; last iApply iThy_le_to_iThy_app.
      iApply iThy_le_trans; last iApply iThy_le_sum_swap.
      iApply iThy_le_trans; last (
      iApply iThy_le_sum_l; iApply iThy_le_sum_to_iThy).
      iApply iThy_le_trans; last iApply iThy_le_sum_assoc_1.
      iApply iThy_le_sum_r.
      iApply iThy_le_trans; last iApply iThy_le_sum_swap.
      iApply iThy_le_trans; last iApply iThy_le_to_iThy_app_inv.
      by iApply IH.
  Qed.

  Lemma iThy_le_to_iThy_bot L X : ⊢ iThy_le (to_iThy (to_iThy_bot L)) X.
  Proof.
    induction L as [|((?,?),?) L]; simpl; [iApply iThy_le_to_iThy_nil|].
    iApply iThy_le_trans; first iApply iThy_le_to_iThy_1.
    iApply IHL.
  Qed.

  Lemma traversable_to_iThy_bot L k1 k2 : ⊢ traversable k1 k2 (to_iThy (to_iThy_bot L)).
  Proof.
    iApply (traversable_le iThyBot); last by iApply traversable_bot.
    - by iApply iThy_le_bot.
    - by iApply (iThy_le_to_iThy_bot L).
  Qed.

  Lemma traversable_to_iThy (L : iLblThy Σ) k1 k2 :
    (∀ l1s, NeutralEctx l1s k1) →
    (∀ l2s, NeutralEctx l2s k2) →
    ⊢ traversable k1 k2 (to_iThy L).
  Proof.
    intros Hk1 Hk2.
    induction L as [|((l1s, l2s), X) L IH];
    first by apply traversable_to_iThy_nil.
    iApply traversable_to_iThy_cons; [|done].
    by iApply traversable_iThyTraverse.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* Ordering of theory lists. *)

  Section to_iThy_le.

    Definition to_iThy_le (L M : iLblThy Σ) : iProp Σ :=
      iThy_le (to_iThy L) (to_iThy M) ∗
      □ (valid M -∗ valid L) ∗
      □ (distinct' M -∗ distinct' L).

    Lemma to_iThy_le_trans (L M N : iLblThy Σ) :
      to_iThy_le L M -∗ to_iThy_le M N -∗ to_iThy_le L N.
    Proof.
      iIntros "(#HLM & #HvalidML & #HdistinctML)
               (#HMN & #HvalidNM & #HdistinctNM)".
      iSplit; [|iSplit].
      { by iApply (iThy_le_trans with "HLM HMN"). }
      { iIntros "!> ?". iApply "HvalidML". by iApply "HvalidNM". }
      { iIntros "!> ?". iApply "HdistinctML". by iApply "HdistinctNM". }
    Qed.

    Lemma iThy_le_submseteq (L M : iLblThy Σ) :
       L ⊆+ M → ⊢ iThy_le (to_iThy L) (to_iThy M).
    Proof.
      induction 1 as [|((l1s, l2s), X) |((l1s, l2s), X) ((l1s', l2s'), Y) L| ???? IH|?????? IH];
      first by iApply iThy_le_refl.
      - iApply iThy_le_trans; first iApply iThy_le_to_iThy_sum.
        iApply iThy_le_trans; last iApply iThy_le_sum_to_iThy.
        by iApply iThy_le_sum_r.
      - iApply iThy_le_trans; first
        iApply (iThy_le_to_iThy_app_inv [_; _] L).
        iApply iThy_le_trans; last
        iApply (iThy_le_to_iThy_app [_; _] L).
        iApply iThy_le_sum_l.
        iApply iThy_le_trans; first
        iApply (iThy_le_to_iThy_app_inv [_] [_]).
        iApply iThy_le_trans; last
        iApply (iThy_le_to_iThy_app [_] [_]).
        by iApply iThy_le_sum_swap.
      - iApply iThy_le_trans; first iApply IH.
        iApply iThy_le_trans; last
        iApply (iThy_le_to_iThy_app [_]).
        by iApply iThy_le_sum_r_2.
      - by iApply iThy_le_trans; last iApply IH.
    Qed.

    Lemma labels_l_app L M : labels_l (L ++ M) = labels_l L ++ labels_l M.
    Proof. by rewrite /labels_l fmap_app fmap_app concat_app. Qed.

    Lemma labels_r_app L M : labels_r (L ++ M) = labels_r L ++ labels_r M.
    Proof. by rewrite /labels_r fmap_app fmap_app concat_app. Qed.
    (* ------------------------------------------------------------------ *)
    (* TODO: move to stdpp_ext *)
    Lemma concat_submseteq {A} (xss yss : list (list A)) :
      xss ⊆+ yss → concat xss ⊆+ concat yss.
    Proof.
      induction 1; first done.
      - by apply submseteq_app.
      - simpl. rewrite !app_assoc. apply submseteq_app; [|done].
        rewrite submseteq_app_r. exists x, y. split; [|split]; try done.
        apply Permutation_app_comm.
      - by apply (submseteq_app []); [apply submseteq_nil_l|].
      - by transitivity (concat l2).
    Qed.

    Lemma submseteq_NoDup {A} (xs ys : list A) : xs ⊆+ ys → NoDup ys → NoDup xs.
    Proof.
      induction 1 as [|? l1 ?? IH| |???? IH|]; first done.
      - rewrite !NoDup_cons.
        intros [Hnotin Hl2]. split; [|by apply IH].
        intros Hin. by apply Hnotin, (elem_of_submseteq l1).
      - rewrite !NoDup_ListNoDup.
        by apply Permutation_NoDup, Permutation_swap.
      - rewrite !NoDup_cons. intros [_ Hl2]. by apply IH.
      - intros Hl3. by auto.
    Qed.
    (* ------------------------------------------------------------------ *)

    Lemma labels_l_submseteq L M : L ⊆+ M → labels_l L ⊆+ labels_l M.
    Proof.
      intros Hsubmseteq. rewrite /labels_l.
      by apply concat_submseteq, fmap_submseteq, fmap_submseteq.
    Qed.

    Lemma labels_r_submseteq L M : L ⊆+ M → labels_r L ⊆+ labels_r M.
    Proof.
      intros Hsubmseteq. rewrite /labels_r.
      by apply concat_submseteq, fmap_submseteq, fmap_submseteq.
    Qed.

    Lemma valid_l_submseteq L M : labels_l L ⊆+ labels_l M → valid_l M -∗ valid_l L.
    Proof.
      intros Hlabels. iIntros "#HM". rewrite /valid_l.
      iApply (big_sepL_submseteq with "HM").
      by apply Hlabels.
    Qed.

    Lemma valid_r_submseteq L M : labels_r L ⊆+ labels_r M → valid_r M -∗ valid_r L.
    Proof.
      intros Hsubmseteq. iIntros "#HM". rewrite /valid_r.
      iApply (big_sepL_submseteq with "HM").
      by apply Hsubmseteq.
    Qed.

    Lemma valid_submseteq' L M :
      labels_l L ⊆+ labels_l M →
      labels_r L ⊆+ labels_r M →
      valid M -∗ valid L.
    Proof.
      intros ??. iIntros "#[HM_l HM_r]". iSplit.
      - by iApply valid_l_submseteq.
      - by iApply valid_r_submseteq.
    Qed.

    Lemma valid_submseteq L M : L ⊆+ M → valid M -∗ valid L.
    Proof.
      intros Hsubmseteq. apply valid_submseteq'.
      - by apply labels_l_submseteq.
      - by apply labels_r_submseteq.
    Qed.

    Lemma distinct_l_submseteq (L M : iLblThy Σ) :
      labels_l L ⊆+ labels_l M → distinct_l M → distinct_l L.
    Proof.
      intros Hsubmseteq HM. rewrite /distinct_l.
      apply (submseteq_NoDup _ (labels_l M)); [|done].
      by apply Hsubmseteq.
    Qed.

    Lemma distinct_r_submseteq (L M : iLblThy Σ) :
      labels_r L ⊆+ labels_r M → distinct_r M → distinct_r L.
    Proof.
      intros Hsubmseteq HM. rewrite /distinct_r.
      apply (submseteq_NoDup _ (labels_r M)); [|done].
      by apply Hsubmseteq.
    Qed.

    Lemma distinct_submseteq' (L M : iLblThy Σ) :
      labels_l L ⊆+ labels_l M →
      labels_r L ⊆+ labels_r M →
      distinct M → distinct L.
    Proof.
      intros ?? [??]. split.
      - by apply (distinct_l_submseteq _ M).
      - by apply (distinct_r_submseteq _ M).
    Qed.

    Lemma distinct_submseteq L M : L ⊆+ M → distinct M → distinct L.
    Proof.
      intros Hsubmseteq. apply distinct_submseteq'.
      - by apply labels_l_submseteq.
      - by apply labels_r_submseteq.
    Qed.

    Lemma to_iThy_le_intro' (L M : iLblThy Σ) : L ⊆+ M → ⊢ to_iThy_le L M.
    Proof.
      intros Hsubmseteq. iSplit; [|iSplit].
      - by iApply iThy_le_submseteq.
      - iIntros "!>". by iApply valid_submseteq.
      - iIntros "!>". iPureIntro. by apply distinct_submseteq.
    Qed.

  End to_iThy_le.

End to_iThy.

(* ------------------------------------------------------------------------- *)
(* Properties of [labels_(l/r)], [valid], and [distinct]. *)

Section basic_properties.
  Context `{!probblazeRGS Σ}.

  Lemma labels_l_cons l1s l2s X (L : _ Σ) :
    labels_l (((l1s, l2s), X) :: L) = l1s ++ labels_l L.
  Proof. done. Qed.

  Lemma labels_r_cons l1s l2s X (L : _ Σ) :
    labels_r (((l1s, l2s), X) :: L) = l2s ++ labels_r L.
  Proof. done. Qed.

  Lemma labels_l_to_iThy_bot (L : _ Σ) :
    labels_l (to_iThy_bot L) = labels_l L.
  Proof.
    induction L as [|((?,?),?) L IH]; simpl; [done|].
    rewrite !labels_l_cons.
    by f_equal.
  Qed.

  Lemma labels_r_to_iThy_bot (L : _ Σ) :
    labels_r (to_iThy_bot L) = labels_r L.
  Proof.
    induction L as [|((?,?),?) L IH]; simpl; [done|].
    rewrite !labels_r_cons.
    by f_equal.
  Qed.

  Lemma elem_of_labels_l l1 l1s l2s X (L : _ Σ) :
    l1 ∈ l1s → ((l1s, l2s), X) ∈ L → l1 ∈ labels_l L.
  Proof.
    revert l1 l1s l2s X.
    induction L as [| ((l1s', l2s'), Y) L IH]; intros l1 l1s l2s X Hin.
    - by rewrite elem_of_nil.
    - rewrite elem_of_cons. intros [Heq|Hin_L]; rewrite labels_l_cons elem_of_app.
      + injection Heq as -> -> ->. by left.
      + right. by apply (IH _ l1s l2s X).
  Qed.

  Lemma elem_of_labels_r l2 l1s l2s X (L : _ Σ) :
    l2 ∈ l2s → ((l1s, l2s), X) ∈ L → l2 ∈ labels_r L.
  Proof.
    revert l2 l1s l2s X.
    induction L as [| ((l1s', l2s'), Y) L IH]; intros l2 l1s l2s X Hin.
    - by rewrite elem_of_nil.
    - rewrite elem_of_cons. intros [Heq|Hin_L]; rewrite labels_r_cons elem_of_app.
      + injection Heq as -> -> ->. by left.
      + right. by apply (IH _ l1s l2s X).
  Qed.

  Lemma distinct_nil : distinct ([] : iLblThy Σ).
  Proof. by split; apply NoDup_nil_2. Qed.

  Lemma valid_nil : ⊢ valid ([] : iLblThy Σ).
  Proof. by iSplit; iApply big_sepL_nil. Qed.

  Lemma is_label_not_in l1 (l1s : list label) :
    is_label l1 (DfracOwn 1) -∗
    ([∗ list] l1' ∈ l1s, is_label l1' DfracDiscarded ) -∗
    ⌜ l1 ∉ l1s ⌝.
  Proof.
    iInduction (l1s) as [|l1' l1s] "IH".
    - iIntros "??"; iPureIntro.
      by apply not_elem_of_nil.
    - iIntros "Hl1 [Hl1' Hl1s]".
      iDestruct ("IH" with "Hl1 Hl1s") as %Hnot_in.
      iDestruct (is_label_ne with "Hl1 Hl1'") as %Hneq.
      iPureIntro.
      by rewrite not_elem_of_cons; auto.
  Qed.

  Lemma distinct_label_l L l1 :
    is_label l1 (DfracOwn 1) -∗ valid_l L -∗ ⌜ l1 ∉ labels_l L ⌝.
  Proof. by iApply is_label_not_in. Qed.

  Lemma spec_label_not_in l2 (l2s : list label) :
    spec_labels_frag l2 (DfracOwn 1) -∗
    ([∗ list] l2' ∈ l2s, spec_labels_frag l2' DfracDiscarded) -∗
    ⌜ l2 ∉ l2s ⌝.
  Proof.
    iInduction (l2s) as [|l2' l2s] "IH".
    - iIntros "??"; iPureIntro.
      by apply not_elem_of_nil.
    - iIntros "Hl2 [Hl2' Hl2s]".
      iDestruct ("IH" with "Hl2 Hl2s") as %Hnot_in.
      iDestruct (spec_label_ne with "Hl2 Hl2'") as %Hneq.
      iPureIntro.
      by rewrite not_elem_of_cons; auto.
  Qed.

  Lemma distinct_label_r L l2 :
    spec_labels_frag l2 (DfracOwn 1) -∗ valid_r L -∗ ⌜ l2 ∉ labels_r L ⌝.
  Proof. by iApply spec_label_not_in. Qed.

  Lemma distinct_l_cons L l1 l1s l2s X :
    let    l1s_l2s_X_L :=       ((l1s, l2s), X) :: L in
    let l1_l1s_l2s_X_L := ((l1 :: l1s, l2s), X) :: L in

    is_label l1 (DfracOwn 1) -∗
    valid_l l1s_l2s_X_L -∗
    ⌜ distinct_l l1s_l2s_X_L ⌝ -∗
    ⌜ distinct_l l1_l1s_l2s_X_L ⌝.
  Proof.
    iIntros (??) "Hl1 #Hvalid %Hdistinct".
    iDestruct (distinct_label_l with "Hl1 Hvalid") as %Hnot_in.
    iPureIntro. by apply NoDup_cons_2.
  Qed.

  Lemma distinct_r_cons L l1s l2 l2s X :
    let    l1s_l2s_X_L :=       ((l1s, l2s), X) :: L in
    let l1s_l2_l2s_X_L := ((l1s, l2 :: l2s), X) :: L in

    spec_labels_frag l2 (DfracOwn 1) -∗
    valid_r l1s_l2s_X_L -∗
    ⌜ distinct_r l1s_l2s_X_L ⌝ -∗
    ⌜ distinct_r l1s_l2_l2s_X_L ⌝.
  Proof.
    iIntros (??) "Hl2 #Hvalid %Hdistinct".
    iDestruct (distinct_label_r with "Hl2 Hvalid") as %Hnot_in.
    iPureIntro. by apply NoDup_cons_2.
  Qed.

  Lemma distinct_l_cons_inv (L : iLblThy Σ) l1s l2s X :
    distinct_l (((l1s, l2s), X) :: L) ↔
    NoDup l1s ∧
    (∀ l1, l1 ∈ l1s → l1 ∉ labels_l L) ∧
    distinct_l L.
  Proof. by rewrite /distinct_l labels_l_cons NoDup_app. Qed.

  Lemma distinct_r_cons_inv (L : iLblThy Σ) l1s l2s X :
    distinct_r (((l1s, l2s), X) :: L) ↔
    NoDup l2s ∧
    (∀ l2, l2 ∈ l2s → l2 ∉ labels_r L) ∧
    distinct_r L.
  Proof. by rewrite /distinct_r labels_r_cons NoDup_app. Qed.

  Lemma distinct_l_cons_cons_inv (L : iLblThy Σ) l1 l1s l2s X :
    distinct_l (((l1 :: l1s, l2s), X) :: L) ↔
    l1 ∉ labels_l (((l1s, l2s), X) :: L) ∧
    distinct_l (((l1s, l2s), X) :: L).
  Proof. by rewrite /distinct_l labels_l_cons NoDup_cons. Qed.

  Lemma distinct_r_cons_cons_inv (L : iLblThy Σ) l2 l1s l2s X :
    distinct_r (((l1s, l2 :: l2s), X) :: L) ↔
    l2 ∉ labels_r (((l1s, l2s), X) :: L) ∧
    distinct_r (((l1s, l2s), X) :: L).
  Proof. by rewrite /distinct_r labels_r_cons NoDup_cons. Qed.

  Lemma distinct_l_to_iThy_bot (L : iLblThy Σ) :
    distinct_l L ↔ distinct_l (to_iThy_bot L).
  Proof.
    induction L as [|((?,?),?) L IH]; simpl; [done|].
    by rewrite !distinct_l_cons_inv labels_l_to_iThy_bot IH.
  Qed.

  Lemma distinct_r_to_iThy_bot (L : iLblThy Σ) :
    distinct_r L ↔ distinct_r (to_iThy_bot L).
  Proof.
    induction L as [|((?,?),?) L IH]; simpl; [done|].
    by rewrite !distinct_r_cons_inv labels_r_to_iThy_bot IH.
  Qed.

  Lemma distinct_to_iThy_bot (L : iLblThy Σ) :
    distinct L ↔ distinct (to_iThy_bot L).
  Proof.
    rewrite /distinct.
    by rewrite distinct_l_to_iThy_bot distinct_r_to_iThy_bot.
  Qed.

  Lemma valid_l_to_iThy_bot (L : iLblThy Σ) :
    valid_l L ∗-∗ valid_l (to_iThy_bot L).
  Proof. by rewrite /valid_l labels_l_to_iThy_bot //=; auto. Qed.

  Lemma valid_r_to_iThy_bot (L : iLblThy Σ) :
    valid_r L ∗-∗ valid_r (to_iThy_bot L).
  Proof. by rewrite /valid_r labels_r_to_iThy_bot //=; auto. Qed.

  Lemma valid_to_iThy_bot (L : iLblThy Σ) :
    valid L ∗-∗ valid (to_iThy_bot L).
  Proof.
    rewrite /valid. iSplit.
    - iIntros "[#? #?]"; iSplit.
      + by iApply (valid_l_to_iThy_bot L).
      + by iApply (valid_r_to_iThy_bot L).
    - iIntros "[#? #?]"; iSplit.
      + by iApply valid_l_to_iThy_bot.
      + by iApply valid_r_to_iThy_bot.
  Qed.

  Definition HandleCtxs (lhrs : list (label * expr * expr)) :=
    map (λ '(l, h, r), HandleCtx l h r) lhrs.

  Lemma NeutralEctx_HandleCtxs_l l2s l1s' l2s' lhr1s X Y (L : iLblThy Σ) :
    ((l1s', l2s'), Y) ∈ L →
    distinct_l ((lhr1s.*1.*1, l2s, X) :: L) →
    NeutralEctx l1s' (HandleCtxs lhr1s).
  Proof.
    induction lhr1s as [|((l1, h1), r1) lhr1s IH].
    { intros _ _; constructor; intros ??. set_solver. }
    intros Hin Hdistinct.
    apply NeutralEctx_cons.
    + constructor. simpl.
      rewrite distinct_l_cons_inv in Hdistinct.
      destruct Hdistinct as (_ & Hnot_in & _).
      intros Hin'.
      apply (Hnot_in l1). { by apply elem_of_cons; left. }
      by apply (elem_of_labels_l _ l1s' l2s' Y).
    + apply IH; try done.
      rewrite distinct_l_cons_cons_inv in Hdistinct.
      by destruct Hdistinct as [_ ?].
  Qed.

  Lemma NeutralEctx_HandleCtxs_r l1s l1s' l2s' lhr2s X Y (L : iLblThy Σ) :
    ((l1s', l2s'), Y) ∈ L →
    distinct_r ((l1s, lhr2s.*1.*1, X) :: L) →
    NeutralEctx l2s' (HandleCtxs lhr2s).
  Proof.
    induction lhr2s as [|((l2, h2), r2) lhr2s IH].
    { intros _ _; constructor; intros ??. set_solver. }
    intros Hin Hdistinct.
    apply NeutralEctx_cons.
    + constructor. simpl.
      rewrite distinct_r_cons_inv in Hdistinct.
      destruct Hdistinct as (_ & Hnot_in & _).
      intros Hin'.
      apply (Hnot_in l2). { by apply elem_of_cons; left. }
      by apply (elem_of_labels_r _ l1s' l2s' Y).
    + apply IH; try done.
      rewrite distinct_r_cons_cons_inv in Hdistinct.
      by destruct Hdistinct as [_ ?].
  Qed.

  Lemma traversable_ectx_labels_aux k1 k2 l1s l2s l1s' l2s' (X Y : iThy Σ) (L : iLblThy Σ) :
    ((l1s', l2s'), Y) ∈ L →
    ectx_labels k1 ⊆ l1s →
    ectx_labels k2 ⊆ l2s →
    distinct (((l1s, l2s), X) :: L) →
    ⊢ traversable k1 k2 (iThyTraverse l1s' l2s' Y).
  Proof.
    intros Hin Hk1 Hk2 [Hdistinct_l Hdistinct_r].
    apply traversable_iThyTraverse.
    - rewrite NeutralEctx_ectx_labels_iff. intros l Hl Hl'.
      rewrite distinct_l_cons_inv in Hdistinct_l.
      destruct Hdistinct_l as [_ [Hnot_in _]].
      apply (Hnot_in l); first by apply Hk1.
      by apply (elem_of_labels_l _ l1s' l2s' Y).
    - apply NeutralEctx_ectx_labels_iff. intros l Hl Hl'.
      rewrite distinct_r_cons_inv in Hdistinct_r.
      destruct Hdistinct_r as [_ [Hnot_in _]].
      apply (Hnot_in l); first by apply Hk2.
      by apply (elem_of_labels_r _ l1s' l2s' Y).
  Qed.

  Lemma traversable_ectx_labels k1 k2 l1s l2s (X : iThy Σ) (L : iLblThy Σ) :
    ectx_labels k1 ⊆ l1s →
    ectx_labels k2 ⊆ l2s →
    distinct (((l1s, l2s), X) :: L) →
    ⊢ traversable k1 k2 (to_iThy L).
  Proof.
    intros Hk1 Hk2 [Hdistinct_l Hdistinct_r].
    induction L as [|((l1s', l2s'), Y) L IH].
    - by apply traversable_to_iThy_nil.
    - iApply (traversable_le (iThySum (iThyTraverse l1s' l2s' Y) (to_iThy L))).
      { by iApply iThy_le_sum_to_iThy. }
      { by iApply iThy_le_to_iThy_sum. }
      iApply traversable_sum.
      + iApply (traversable_ectx_labels_aux _ _ l1s l2s _ _ X _ ((l1s', l2s', Y) :: L));
        try done; set_solver.
      + iApply IH.
        * rewrite !distinct_l_cons_inv in Hdistinct_l.
          rewrite distinct_l_cons_inv.
          destruct Hdistinct_l as (Hlhr1s & Hnot_in & (_&_&HL)).
          split; [|split]; try done.
          intros l1 Hin Hin'. apply (Hnot_in l1 Hin).
          rewrite labels_l_cons. set_solver.
        * rewrite !distinct_r_cons_inv in Hdistinct_r.
          rewrite distinct_r_cons_inv.
          destruct Hdistinct_r as (Hlhr2s & Hnot_in & (_&_&HL)).
          split; [|split]; try done.
          intros l2 Hin Hin'. apply (Hnot_in l2 Hin).
          rewrite labels_r_cons. set_solver.
  Qed.

  Lemma ectx_labels_HandleCtxs lhrs : ectx_labels (HandleCtxs lhrs) = lhrs.*1.*1.
  Proof.
    induction lhrs as [|((l, h), r) lhrs IH]; [done|].
    by rewrite !fmap_cons -IH.
  Qed.

  Lemma traversable_HandleCtxs (X : iThy Σ) L l1s l2s lhr1s lhr2s :
    lhr1s.*1.*1 = l1s →
    lhr2s.*1.*1 = l2s →
    distinct (((l1s, l2s), X) :: L) →
    ⊢ traversable (HandleCtxs lhr1s) (HandleCtxs lhr2s) (to_iThy L).
  Proof.
    intros <- <- Hdistinct.
    apply (traversable_ectx_labels _ _ lhr1s.*1.*1 lhr2s.*1.*1 X); last done;
    by rewrite ectx_labels_HandleCtxs.
  Qed.

End basic_properties.


  
(* ------------------------------------------------------------------------- *)
(* blaze: Reasoning rules. *)

Section blaze_rules.
  Context `{!probblazeRGS Σ}.

  Lemma brel_learn e1 e2 L R :
    (distinct' L -∗ valid L -∗ BREL e1 ≤ e2 <|L|> {{R}}) ⊢ BREL e1 ≤ e2 <|L|> {{R}}.
  Proof. iIntros "Hbrel #? %". by iApply "Hbrel". Qed.

  Lemma brel_change e1 e2 L R :
    distinct' L -∗
    valid L -∗
    BREL e1 ≤ e2 <|to_iThy_bot L|> {{R}} -∗
    BREL e1 ≤ e2 <|[]|> {{R}}.
  Proof.
    iIntros "[% %] [#Hvalid_l #Hvalid_r] Hbrel _ _".
    iApply (rel_introduction_mono with "[Hbrel]"); last (
    iApply (iThy_le_to_iThy_bot L)).
    iApply "Hbrel".
    { iSplit.
      - by iApply (valid_l_to_iThy_bot L).
      - by iApply (valid_r_to_iThy_bot L).
    }
    { iSplit; iPureIntro.
      - by rewrite -distinct_l_to_iThy_bot.
      - by rewrite -distinct_r_to_iThy_bot.
    }
  Qed.

  Lemma brel_value (v1 v2 : val) L R : R v1 v2 ⊢ BREL v1 ≤ v2 <|L|> {{R}}.
  Proof. iIntros "HR _ _". by iApply rel_value. Qed.

  Lemma brel_wand e1 e2 L R S :
    BREL e1 ≤ e2 <|L|> {{R}} -∗ □ (∀ v1 v2, R v1 v2 -∗ S v1 v2) -∗
    BREL e1 ≤ e2 <|L|> {{S}}.
  Proof.
    iIntros "Hbrel #HR #Hvalid #Hdistinct".
    iApply (rel_wand with "[Hbrel] HR").
    by iApply "Hbrel".
  Qed.

  Lemma brel_wand' e1 e2 L R S :
    □ (∀ v1 v2, R v1 v2 -∗ S v1 v2) -∗
    BREL e1 ≤ e2 <|L|> {{R}} -∗
    BREL e1 ≤ e2 <|L|> {{S}}.
  Proof. by iIntros "#HR Hbrel"; iApply (brel_wand with "Hbrel HR"). Qed.

  Lemma brel_introduction l1s l2s X Q e1 e2 L R :
    ((l1s, l2s), X) ∈ L →
    iThyTraverse l1s l2s X e1 e2 Q -∗
    □ ▷ (∀ s1 s2, Q s1 s2 -∗ BREL s1 ≤ s2 <|L|> {{R}}) -∗
    BREL e1 ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "%Hin HX #Hbrel #Hvalid %Hdistinct".
    iApply (rel_introduction with "[HX]").
    { iExists l1s, l2s, X. by iFrame. }
    iIntros "!> !> %s1 %s2 HQ".
    by iApply ("Hbrel" with "HQ").
  Qed.

  Lemma brel_introduction' l1s l2s X e1 e2 L R :
    ((l1s, l2s), X) ∈ L →
    iThyTraverse l1s l2s X e1 e2 (λ s1 s2, BREL s1 ≤ s2 <|L|> {{R}}) -∗
    BREL e1 ≤ e2 <|L|> {{R}}.
  Proof.
    set Q : _ → _ → iProp Σ := (λ s1 s2, BREL s1 ≤ s2 <|L|> {{R}})%I.
    iIntros (Hin) "HX".
    by iApply (brel_introduction _ _ _ Q with "HX"); last auto.
  Qed.

  Lemma fupd_brel e1 e2 L R :
    (|={⊤}=> BREL e1 ≤ e2 <|L|> {{R}}) ⊢ BREL e1 ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "H #Hvalid %Hdistinct". iApply fupd_rel.
    iMod "H". iApply ("H" with "Hvalid [//]").
  Qed.

  Lemma brel_pure_step_later `{!probblazeGS Σ} e1 e1' e2 φ n L R :
    PureExec φ n e1 e1' →
    φ →
    ▷^n (BREL e1' ≤ e2 <|L|> {{R}}) ⊢ BREL e1 ≤ e2 <|L|> {{R}}.
  Proof.
    intros Hexec ?.
    iIntros "Hbrel #Hvalid #Hdistinct".
    iApply rel_pure_step_l; first done.
    iIntros "!>". by iApply "Hbrel".
  Qed.

  Lemma brel_pure_step_r `{!probblazeGS Σ} e1 e2 e2' φ n L R :
    PureExec φ n e2 e2' →
    φ →
    BREL e1 ≤ e2' <|L|> {{R}} ⊢ BREL e1 ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros (Hexec Hφ) "Hbrel #Hvalid %Hdistinct".
    iApply (rel_pure_step_r _ _ e2' _ φ n). { done. }
    by iApply "Hbrel".
  Qed.

End blaze_rules.

(* ------------------------------------------------------------------------- *)
(* blaze: Reasoning Rules about State. *)

Section blaze_rules_state_rules.
  Context `{!probblazeRGS Σ}.

  Lemma brel_alloc_l L R k1 v1 e2 :
    ▷ (∀ l1, l1 ↦ v1 -∗ BREL fill k1 #l1 ≤ e2 <|L|> {{R}}) -∗
    BREL fill k1 (ref v1) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hbrel #Hvalid %Hdistinct".
    iApply rel_alloc_l.
    iIntros "!> %l1 Hl1".
    iApply ("Hbrel" with "Hl1 [//] [//]").
  Qed.

  Lemma brel_alloc_r L R e1 k2 v2 :
    (∀ l2, l2 ↦ₛ v2 -∗ BREL e1 ≤ fill k2 #l2 <|L|> {{R}}) -∗
    BREL e1 ≤ fill k2 (ref v2) <|L|> {{R}}.
  Proof.
    iIntros "Hbrel #Hvalid %Hdistinct".
    iApply rel_alloc_r.
    iIntros "%l2 Hl2".
    iApply ("Hbrel" with "Hl2 [//] [//]").
  Qed.

  Lemma brel_load_l L R k1 l1 dq1 v1 e2 :
    ▷ l1 ↦{dq1} v1 -∗
    ▷ (l1 ↦{dq1} v1 -∗ BREL fill k1 v1 ≤ e2 <|L|> {{R}}) -∗
    BREL fill k1 (! #l1) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hl1 Hbrel #Hvalid %Hdistinct".
    iApply (rel_load_l with "Hl1").
    iIntros "!> Hl1".
    iApply ("Hbrel" with "Hl1 [//] [//]").
  Qed.

  Lemma brel_load_r L R e1 k2 l2 dq2 v2 :
    l2 ↦ₛ{dq2} v2 -∗
    (l2 ↦ₛ{dq2} v2 -∗ BREL e1 ≤ fill k2 v2 <|L|> {{R}}) -∗
    BREL e1 ≤ fill k2 (! #l2) <|L|> {{R}}.
  Proof.
    iIntros "Hl2 Hbrel #Hvalid %Hdistinct".
    iApply (rel_load_r with "Hl2").
    iIntros "Hl2".
    iApply ("Hbrel" with "Hl2 [//] [//]").
  Qed.

  Lemma brel_store_l L R k1 l1 v1 w1 e2 :
    ▷ l1 ↦ v1 -∗
    ▷ (l1 ↦ w1 -∗ BREL fill k1 #(()%V) ≤ e2 <|L|> {{R}}) -∗
    BREL fill k1 (#l1 <- w1) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hl1 Hbrel #Hvalid %Hdistinct".
    iApply (rel_store_l with "Hl1").
    iIntros "!> Hl1".
    iApply ("Hbrel" with "Hl1 [//] [//]").
  Qed.

  Lemma brel_store_r L R e1 k2 l2 v2 w2 :
    l2 ↦ₛ v2 -∗
    (l2 ↦ₛ w2 -∗ BREL e1 ≤ fill k2 #(()%V) <|L|> {{R}}) -∗
    BREL e1 ≤ fill k2 (#l2 <- w2) <|L|> {{R}}.
  Proof.
    iIntros "Hl2 Hbrel #Hvalid %Hdistinct".
    iApply (rel_store_r with "Hl2").
    iIntros "Hl2".
    iApply ("Hbrel" with "Hl2 [//] [//]").
  Qed.

End blaze_rules_state_rules.

(* ------------------------------------------------------------------------- *)
(* blaze: Rules for Allocating Effects and Managing Theories. *)

Section brel_effect_rules.
  Context `{!probblazeRGS Σ}.

  Lemma brel_effect_l L R k1 s1 e1 e2 :
    (▷ ∀ l1, is_label l1 (DfracOwn 1) ==∗
      BREL fill k1 (lbl_subst s1 l1 e1) ≤ e2 <|L|> {{R}}
    ) -∗
    BREL fill k1 (Effect s1 e1) ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hbrel #Hvalid %Hdistinct".
    iApply rel_effect_l. iIntros "!> %l1 Hl1".
    by iApply ("Hbrel" with "Hl1").
  Qed.

  Lemma brel_effect_r L R e1 k2 s2 e2 :
    (∀ l2, spec_labels_frag l2 (DfracOwn 1) ==∗
      BREL e1 ≤ fill k2 (lbl_subst s2 l2 e2) <|L|> {{R}}
    ) -∗
    BREL e1 ≤ fill k2 (Effect s2 e2) <|L|> {{R}}.
  Proof.
    iIntros "Hbrel #Hvalid %Hdistinct".
    iApply rel_effect_r. iIntros "%l2 Hl2".
    by iApply ("Hbrel" with "Hl2").
  Qed.

   Lemma brel_new_theory e1 e2 L R :
    BREL e1 ≤ e2 <|([], [], iThyBot) :: L|> {{R}} -∗
    BREL e1 ≤ e2 <|L|> {{R}}.
  Proof.
    iIntros "Hbrel [#Hvalid_l #Hvalid_r] [%Hdistinct_l %Hdistinct_r]".
    iApply (rel_introduction_mono with "[Hbrel]").
    { iApply "Hbrel".
      - iSplit.
        + by rewrite /valid_l labels_l_cons //=.
        + by rewrite /valid_r labels_r_cons //=.
      - iPureIntro. split.
        + by rewrite /distinct_l labels_l_cons.
        + by rewrite /distinct_r labels_r_cons.
    }
    { by iApply iThy_le_to_iThy_1. }
  Qed.

   Lemma brel_add_label_l e1 e2 l1 l1s l2s L R :
    is_label l1 (DfracOwn 1) -∗
    BREL e1 ≤ e2 <|((l1 :: l1s, l2s, iThyBot) :: L)|> {{R}} -∗
    BREL e1 ≤ e2 <|((l1s, l2s, iThyBot) :: L)|> {{R}}.
  Proof.
    iIntros "Hl1 Hbrel
      [#Hvalid_l1s #Hvalid_l2s]
      [%Hdistinct_l1s %Hdistinct_l2s]".
    iDestruct (distinct_l_cons with "[$] [$] [//]") as %Hdistinct_cons_l1s.
    iApply fupd_rel.
    iMod (is_label_persist with "Hl1") as "#Hl1". iModIntro.
    iSpecialize ("Hbrel" with "[] []").
    { iSplit; [|done]. rewrite !/valid_l !labels_l_cons //=. by iSplit. }
    { by iSplit. }
    iApply (rel_introduction_mono with "Hbrel").
    iApply (iThy_le_trans _ (to_iThy L)).
    { by iApply iThy_le_to_iThy_1. }
    { by iApply iThy_le_to_iThy_2. }
  Qed.

  Lemma brel_add_label_r e1 e2 l1s l2 l2s L R :
    spec_labels_frag l2 (DfracOwn 1) -∗
    BREL e1 ≤ e2 <|((l1s, l2 :: l2s, iThyBot) :: L)|> {{R}} -∗
    BREL e1 ≤ e2 <|((l1s, l2s, iThyBot) :: L)|> {{R}}.
  Proof.
    iIntros "Hl2 Hbrel
      [#Hvalid_l1s #Hvalid_l2s]
      [%Hdistinct_l1s %Hdistinct_l2s]".
    iDestruct (distinct_r_cons with "[$] [$] [//]") as %Hdistinct_cons_l2s.
    iApply fupd_rel.
    iMod (spec_label_persist with "Hl2") as "#Hl2". iModIntro.
    iSpecialize ("Hbrel" with "[] []").
    { iSplit; [done|]. rewrite !/valid_r !labels_r_cons //=. by iSplit. }
    { by iSplit. }
    iApply (rel_introduction_mono with "Hbrel").
    iApply (iThy_le_trans _ (to_iThy L)).
    { by iApply iThy_le_to_iThy_1. }
    { by iApply iThy_le_to_iThy_2. }
  Qed.

  Lemma brel_exhaustion e1 e2 k1 k2 (X Y : iThy Σ) L R S l1s l2s :
    ectx_labels k1 ⊆ l1s →
    ectx_labels k2 ⊆ l2s →

    BREL e1 ≤ e2 <|((l1s, l2s, X) :: L)|> {{R}} -∗

    ((* Value case. *)
      (□ ∀ v1 v2,
      R v1 v2 -∗
      BREL fill k1 v1 ≤ fill k2 v2 <|((l1s, l2s, Y) :: L)|> {{S}})

      ∧

     (* Effect case. *)
      (□ ∀ k1' k2' e1' e2' Q,
      ⌜ NeutralEctx l1s k1' ⌝ →
      ⌜ NeutralEctx l2s k2' ⌝ →
      X e1' e2' Q -∗
      (□ ▷ ∀ s1' s2', Q s1' s2' -∗
      BREL fill k1' s1' ≤ fill k2' s2' <|((l1s, l2s, X) :: L)|> {{R}}) -∗
      BREL fill (k1 ++ k1') e1' ≤ fill (k2 ++ k2') e2' <|((l1s, l2s, Y) :: L)|> {{S}})
    ) -∗

    BREL fill k1 e1 ≤ fill k2 e2 <|((l1s, l2s, Y) :: L)|> {{S}}.
  Proof.
    iIntros (Hk1 Hk2) "Hbrel [#Hvalue #Heffect] #Hvalid %Hdistinct".
    iApply (rel_introduction_mono with "[Hbrel]"); last iApply iThy_le_sum_to_iThy.
    iApply (rel_exhaustion_sum_r  with "[] [Hbrel]").
    { by iApply (traversable_ectx_labels k1 k2 l1s l2s X). }
    { iApply (rel_introduction_mono with "[Hbrel]").
      { by iApply "Hbrel". } { by iApply iThy_le_to_iThy_sum. }
    }
    clear e1 e2. simpl.
    iIntros "!>". iSplit.
    - iIntros (v1 v2) "HR".
      iApply (rel_introduction_mono with "[HR]"); last iApply iThy_le_to_iThy_sum.
      by iApply ("Hvalue" with "HR").
    - iIntros "%e1 %e2 %Q HX #Hk".
      iDestruct "HX" as
        "[%e1' [%e2' [%k1' [%k2' [%Q' (-> & % & -> & % & HX & # HQ')]]]]]".
      iApply (rel_introduction_mono with "[HX]"); last iApply iThy_le_to_iThy_sum.
      rewrite -!fill_app.
      iApply ("Heffect" with "[//] [//] HX"); try done.
      iIntros "!> !> %s1' %s2' HQ".
      iSpecialize ("HQ'" with "HQ").
      iSpecialize ("Hk" with "HQ'").
      iIntros "_ _".
      iApply (rel_introduction_mono with "[Hk]"); last iApply iThy_le_sum_to_iThy.
      iApply "Hk".
  Qed.

   Lemma brel_bind k1 k2 (L M : iLblThy Σ) R e1 e2 :
    traversable k1 k2 (to_iThy L) -∗
    to_iThy_le L M -∗
    BREL e1 ≤ e2 <|L|> {{ (λ v1 v2, BREL fill k1 v1 ≤ fill k2 v2 <|M|> {{R}}) }} -∗
    BREL fill k1 e1 ≤ fill k2 e2 <|M|> {{R}}.
  Proof.
    iIntros "#Htraversable (#Hle & #HvalidLM & #HdistinctLM) Hbrel #Hvalid %Hdistinct".
    iApply (rel_bind with "[] Hle [Hbrel]"); first iApply "Htraversable".
    iApply (rel_wand with "[Hbrel]").
    { by iApply "Hbrel"; [iApply "HvalidLM"|iApply "HdistinctLM"]. }
    { iIntros "!> %% Hbrel". by iApply "Hbrel". }
  Qed.

  Lemma brel_bind' k1 k2 (L : iLblThy Σ) R e1 e2 :
    traversable k1 k2 (to_iThy L) -∗
    BREL e1 ≤ e2 <|L|> {{ (λ v1 v2, BREL fill k1 v1 ≤ fill k2 v2 <|L|> {{R}}) }} -∗
    BREL fill k1 e1 ≤ fill k2 e2 <|L|> {{R}}.
  Proof.
    iIntros "#Htraversable Hbrel #Hvalid %Hdistinct".
    iApply (rel_bind' with "[] [Hbrel]"); first iApply "Htraversable".
    iApply (rel_wand with "[Hbrel]").
    { by iApply "Hbrel". }
    { iIntros "!> %% Hbrel". by iApply "Hbrel". }
  Qed.

  Lemma distinct_l_app_NeutralEctx k1 l1s l2s X (L M : iLblThy Σ) :
    distinct_l (L ++ M) →
    ectx_labels k1 ⊆ labels_l M →
    (l1s, l2s, X) ∈ L →
    NeutralEctx l1s k1.
  Proof.
    intros Hdistinct Hincl Hin_L. constructor=> l Hin_l1s Hin_k1.
    cut (l ∈ labels_l M); [|by apply Hincl]. intros Hin_labels_M.
    have Hin_labels_L: l ∈ labels_l L.
    { by apply (elem_of_labels_l _ l1s l2s X). }
    rewrite /distinct_l labels_l_app NoDup_app in Hdistinct.
    destruct Hdistinct as (_&Hdistinct&_).
    by apply (Hdistinct l).
  Qed.

  Lemma distinct_r_app_NeutralEctx k2 l1s l2s X (L M : iLblThy Σ) :
    distinct_r (L ++ M) →
    ectx_labels k2 ⊆ labels_r M →
    (l1s, l2s, X) ∈ L →
    NeutralEctx l2s k2.
  Proof.
    intros Hdistinct Hincl Hin_L. constructor=> l Hin_l1s Hin_k2.
    cut (l ∈ labels_r M); [|by apply Hincl]. intros Hin_labels_M.
    have Hin_labels_L: l ∈ labels_r L.
    { by apply (elem_of_labels_r _ l1s l2s X). }
    rewrite /distinct_r labels_r_app NoDup_app in Hdistinct.
    destruct Hdistinct as (_&Hdistinct&_).
    by apply (Hdistinct l).
  Qed.

  Lemma brel_bind'' k1 k2 (L M N : iLblThy Σ) R e1 e2 :
    ectx_labels k1 ⊆ labels_l M →
    ectx_labels k2 ⊆ labels_r M →
    to_iThy_le (L ++ M) N -∗
    BREL e1 ≤ e2 <|L|> {{ (λ v1 v2, BREL fill k1 v1 ≤ fill k2 v2 <|N|> {{R}}) }} -∗
    BREL fill k1 e1 ≤ fill k2 e2 <|N|> {{R}}.
  Proof.
    iIntros "%Hlabels_l %Hlabels_r #Hto_iThy_le Hbrel".
    iAssert (□ (_ ∗ _ ∗ _))%I as "(#Hle & #Hvalid & #Hdistinct)".
    { iIntros "!>". by iApply "Hto_iThy_le". }
    iApply brel_learn.
    iIntros "#Hdistinct_N #Hvalid_N".
    iApply (brel_bind with "[] [] Hbrel").
    { iIntros "!>" (e1' e2' Q) "[%l1s [%l2s [%X [%Hin HL]]]]".
      iDestruct ("Hdistinct" with "Hdistinct_N") as "[%Hl %Hr]".
      specialize (distinct_l_app_NeutralEctx _ _ _ _ _ _ Hl Hlabels_l Hin) as Hk1.
      specialize (distinct_r_app_NeutralEctx _ _ _ _ _ _ Hr Hlabels_r Hin) as Hk2.
      iPoseProof (traversable_iThyTraverse _ _ X _ _ Hk1 Hk2) as "HX".
      iDestruct ("HX" with "HL") as "[%Q' [HX' HQ']]".
      iExists Q'. iSplitL "HX'".
      { iExists l1s, l2s, X. by iFrame. } { done. }
    }
    { iApply to_iThy_le_trans; last iApply "Hto_iThy_le".
      iApply to_iThy_le_intro'.
      apply submseteq_inserts_r.
      reflexivity.
    }
  Qed.

End brel_effect_rules.

Section brel_probabilistic_rules.
 Context `{!probblazeRGS Σ}.

 Lemma brel_couple_rand_rand N f `{Bij nat nat f} z K K' X R :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) →
    (∀ n : nat, BREL fill K #(n) ≤ fill K' #(f n) <|X|> {{R}})
        ⊢ BREL fill K (rand #z) ≤ fill K' (rand #z) <|X|> {{R}}.
  Proof.
    iIntros (??)  "Hrel #Hvalid Hdistinct".
    iApply rel_couple_rand_rand; [done|].
    iIntros (n).
    by iApply "Hrel".
  Qed.

  Lemma brel_randT_r K α N z n ns t X R :
    TCEq N (Z.to_nat z) →
    α ↪ₛN (N; n :: ns)
   ⊢ (α ↪ₛN (N; ns)-∗ ⌜ n ≤ N ⌝ -∗ BREL t ≤ fill K (of_val #n) <|X|> {{R}})
    -∗ BREL t ≤ (fill K (rand(#lbl:α) #z)) <|X|> {{R}}.
  Proof.
    iIntros (?) "Hα Hrel #Hvalid Hdistinct".
    iApply (rel_randT_r with "[$]"). 
    iIntros "Hα Hlt".
    by iApply ("Hrel" with "[$][$]").
  Qed.
  Definition brel_rand_r := brel_randT_r.

  Lemma brel_randT_empty_r K α N z e X R :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛN (N; []) ∗
      (∀ n : nat, α ↪ₛN (N; []) -∗ ⌜ n ≤ N ⌝ -∗ BREL e ≤ fill K (Val #n) <|X|> {{R}})
    ⊢ BREL e ≤ fill K (rand(#lbl:α) #z) <|X|> {{R}}.
  Proof.
    iIntros (?) "(Hα & Hrel) #Hvalid Hdistinct".
    iApply (rel_randT_empty_r). iFrame.
    iIntros (n) "Hα Hlt".
    by iApply ("Hrel" with "[$][$]").
  Qed.
  Definition brel_rand_empty_r := brel_randT_empty_r.

  Lemma brel_randT_l K α N z n ns t X R :
    TCEq N (Z.to_nat z) →
    (▷ α ↪N (N; n :: ns) ∗
     ▷ (α ↪N (N; ns) -∗ ⌜ n ≤ N ⌝ -∗ BREL fill K (of_val #n) ≤ t <|X|> {{R}}))
    ⊢ BREL fill K (rand(#lbl:α) #z) ≤ t <|X|> {{R}}.
  Proof.
    iIntros (?) "(Hα & Hrel) #Hvalid Hdistinct".
    iApply (rel_randT_l). iFrame.
    iIntros "!> Hα Hlt".
    by iApply ("Hrel" with "[$][$]").
  Qed.
  Definition brel_rand_l := brel_randT_l.

  Lemma brel_randT_empty_l K α N z e X R :
    TCEq N (Z.to_nat z) →
    ▷ α ↪N (N; []) ∗
    ▷ (∀ (n : nat), α ↪N (N; []) -∗ ⌜ n ≤ N ⌝ -∗ BREL fill K (Val #n) ≤ e <|X|> {{R}})
    ⊢ BREL fill K (rand(#lbl:α) #z) ≤ e <|X|> {{R}}.
  Proof.
    iIntros (?) "(Hα & Hrel) #Hvalid Hdistinct".
    iApply (rel_randT_empty_l). iFrame.
    iIntros (n) "!> Hα Hlt".
    by iApply ("Hrel" with "[$][$]").
  Qed.
  Definition brel_rand_empty_l := brel_randT_empty_l.

  Lemma brel_couple_couple_avoid (N:nat) l z K K' X R:
    NoDup l ->
    TCEq N (Z.to_nat z) →
    ↯ (length l / (S N)) ∗
    ▷ (∀ (n : fin (S N)), ⌜n ∉ l⌝ -∗ BREL fill K (Val #n) ≤ fill K' (Val #n) <|X|> {{R}})
    ⊢ BREL fill K (rand #z) ≤ fill K' (rand #z) <|X|> {{R}}.
  Proof.
    iIntros (??) "(Hα & Hrel) #Hvalid Hdistinct".
    iApply (rel_couple_couple_avoid); first done. iFrame.
    iIntros (n) "!>Hnin".
    by iApply ("Hrel" with "[$][$]").
  Qed.
    
  Lemma brel_couple_TT_frag (N M : nat) (f : nat -> nat) {_ : Inj (=) (=) f} e1 e2 X R α αₛ ns nsₛ :
    (M <= N)%nat →
    (∀ n : nat, n < S M → f n < S N)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (n : nat),
        ⌜ n ≤ N ⌝ -∗
        if bool_decide (∃ m, m ≤ M /\ f m = n) then
          ∀ m, α ↪N (N; ns ++ [f m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜f m ≤ N⌝ ∗ ⌜m ≤ M⌝ -∗
               BREL e1 ≤ e2 <|X|> {{R}}
        else
          α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗ BREL e1 ≤ e2 <|X|> {{R}}
    )
    ⊢ BREL e1 ≤ e2 <|X|> {{R}}.
  Proof.
    iIntros (??) "(Hα & Hαs & Hrel) #Hvalid Hdistinct".
    iApply (rel_couple_TT_frag); try done. iFrame.
    iIntros (n) "Hlt".
    iSpecialize ("Hrel" $! n with "Hlt"). 
    case_bool_decide; iIntros;
      by iApply ("Hrel" with "[$][$]").
  Qed.

  Lemma brel_couple_TT_adv (N M : nat) (f : nat → nat) {_ : Inj (=) (=) f} e1 e2 X A α αₛ ns nsₛ (ε : R) :
    (0 <= ε)%R →
    (N < M)%nat →
    (∀ n : nat, n < S N → f n < S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗
    (∀ (m : nat),
        ⌜ m ≤ M ⌝ -∗
        if bool_decide (∃ n, n ≤ N /\ f n = m) then
          ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜n ≤ N⌝ ∗ ⌜f n ≤ M⌝ -∗
               BREL e1 ≤ e2 <|X|> {{A}}
        else
          ∀ (ε' : R),
            ⌜ε' = ((S M) / (S M - S N) * ε)%R⌝ ∗
            α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗
            BREL e1 ≤ e2 <|X|> {{A}})
    ⊢ BREL e1 ≤ e2 <|X|> {{A}}.
  Proof.
    iIntros (???) "(Hα & Hαs & Herr & Hrel) #Hvalid Hdistinct".
    iApply (rel_couple_TT_adv); try done. iFrame.
    iIntros (m) "Hlt".
    iSpecialize ("Hrel" $! m with "Hlt"). 
    case_bool_decide; iIntros;
      by iApply ("Hrel" with "[$][$]").
  Qed.

  (* Error credit amplification *)
  Lemma brel_get_ec e e' X A :
    (∀ ε : R, (↯ ε) -∗ ⌜(0 < ε)%R⌝ -∗ BREL e ≤ e' <|X|> {{A}}) ⊢
    (BREL e ≤ e' <|X|> {{A}}).
  Proof.
    iIntros "H Hvalid Hdistinct".
    iApply rel_get_ec. 
    iIntros. by iApply ("H" with "[$][][$]").
  Qed.

  Lemma brel_ind_amp e e' X A (k : R) :
    (1 < k)%R ->
    □ (∀ (ε : R),
          ⌜(0 < ε)%R⌝ -∗ □(↯ (k * ε) -∗ (BREL e ≤ e' <|X|> {{A}}))
                         -∗ ↯ ε -∗ (BREL e ≤ e' <|X|> {{A}}))%I
    ⊢ BREL e ≤ e' <|X|> {{A}}.
  Proof.
    iIntros (?) "#H #Hvalid #Hdistinct".
    iApply rel_ind_amp; first done.
    iModIntro. iIntros (ε) "? #Hind ?".
    iApply ("H" with "[$][Hind][$][$][$]"). 
    iModIntro. iIntros "? ? ?".
    by iApply ("Hind" with "[$]").
  Qed.  

End brel_probabilistic_rules.

