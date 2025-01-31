(** * Hocap atomic rand specs
    The sampling operation is atomic. This allows tapes to be placed within invariants
 *)
From clutch.coneris Require Import coneris atomic.

Set Default Proof Using "Type*".

Class rand_atomic_spec (tb:nat) `{!conerisGS Σ} := RandAtomicSpec
{
  (** * Operations *)
  rand_allocate_tape : val;
  rand_tape : val;
  (** * Ghost state *)

  
  (** * Predicates *)
  rand_tapes (α:val) (ns: (list nat)): iProp Σ;
  (** * General properties of the predicates *)
  (* #[global] rand_tapes_auth_timeless {L : randG Σ} γ m :: *)
  (*   Timeless (rand_tapes_auth (L:=L) γ m); *)
  #[global] rand_tapes_timeless α ns::
    Timeless (rand_tapes α ns);  
  (* #[global] rand_tape_name_inhabited :: *)
  (*   Inhabited rand_tape_name; *)

  (* rand_tapes_auth_exclusive {L : randG Σ} γ m m': *)
  (* rand_tapes_auth (L:=L) γ m -∗ rand_tapes_auth (L:=L) γ m' -∗ False; *)
  rand_tapes_exclusive α ns ns':
  rand_tapes α ns-∗ rand_tapes α ns'-∗ False;
  (* rand_tapes_agree {L : randG Σ} γ α m ns: *)
  (* rand_tapes_auth (L:=L) γ m -∗ rand_tapes (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝; *)
  rand_tapes_valid α ns:
    rand_tapes α ns -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ; 
  (* rand_tapes_update {L : randG Σ} γ α m ns ns': *)
  (* Forall (λ x, x<=ns'.1) ns'.2 -> *)
  (*   rand_tapes_auth (L:=L) γ m -∗ rand_tapes (L:=L) γ α ns ==∗ *)
  (*   rand_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ rand_tapes (L:=L) γ α ns'; *)
  rand_tapes_presample E α ns ε (ε2 : fin (S tb) -> R):
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / (S tb) * ε2 n)%R <= ε)%R ->
  rand_tapes α ns-∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ rand_tapes α (ns ++ [fin_to_nat n])); 
    

  (** * Program specs *)
  
  rand_allocate_tape_spec E :
    {{{ True }}}
      rand_allocate_tape #() @ E
      {{{ (v:val), RET v;
           rand_tapes v []
      }}}; 
  
  rand_tape_spec_some E (α:val):
    ⊢(<<{∀∀ n ns, rand_tapes α (n::ns) }>>
      rand_tape α @ E
             <<{  rand_tapes α ns |RET #n }>>)%I
}.


Section checks.
  Context `{H: conerisGS Σ, r1:!rand_atomic_spec tb}.
  Lemma wp_atomic_rand_tape_1 n ns α :
     rand_tapes α (n :: ns) -∗
      WP (rand_tape α)%E 
             {{ λ n', ⌜#n=n'⌝∗  rand_tapes α (ns) ∗ ⌜ (n<=tb)%nat⌝ }}.
  Proof.
    iIntros "Hfrag".
    iDestruct (rand_tapes_valid with "[$]") as "%H'".
    awp_apply (rand_tape_spec_some ∅ with "[-]").
    iAaccIntro with "Hfrag".
    - iIntros "?". by iFrame.
    -  iIntros. iFrame. iModIntro. iSplit; first done.
       iPureIntro.
       rewrite Forall_cons in H'. naive_solver.
  Qed.

End checks.


Section impl.
  Local Opaque INR.
  Variable tb:nat.
  Context `{!conerisGS Σ}.

  Definition rand_tapes1 α ns := (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (tb; ns) ))%I.

  #[local] Program Definition rand_atomic_spec1 : rand_atomic_spec tb :=
    {| rand_allocate_tape:= (λ: "_", alloc #tb);
      rand_tape:= (λ: "α", rand("α") #tb); 
      rand_tapes := rand_tapes1;
    |}.
  Next Obligation.
    simpl.
    iIntros (???) "(%&%&H1) (%&%&H2)".
    simplify_eq.
    iDestruct (tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "(%&?&H1)".
    iApply (tapeN_ineq with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "(%&%&?)?".
    by iMod (state_update_presample_exp with "[$][$]") as "(%&$&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (? Φ) "_ HΦ".
    wp_pures.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (?? Φ) "AU".
    wp_pures.
    iApply fupd_pgl_wp.
    iMod "AU" as "(%&%&(%&%&Ht)&[AU _])".
    simplify_eq.
    iMod ("AU" with "[$Ht//]") as "AU".
    iModIntro.
    iMod ("AU") as "(%&%&(%&%&Ht)&[_ AU])".
    simplify_eq.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    by iMod ("AU" with "[$Htape//]").
  Qed.
End impl.


Section impl3.
  (* We name it impl3 since it is the rejection sampler example*)
  Context `{!conerisGS Σ}.
  Variable tb:nat.
  Local Opaque INR.
  Definition rand_tapes3 α ns :=
    ((∃ α' ns', ⌜#lbl:α'=α⌝ ∗ ⌜filter (λ x, x<=tb)%nat ns' = ns⌝ ∗ α'↪N (S tb; ns')))%I.
  
  #[local] Program Definition rand_atomic_spec3 : rand_atomic_spec tb :=
    {| rand_allocate_tape:= (λ: "_", alloc #(S tb));
      rand_tape:= (rec: "f" "α":=
                     let: "res" := rand("α") #(S tb) in
                     if: "res" ≤ #tb then "res" else "f" "α"
                  ); 
      rand_tapes := rand_tapes3;
    |}.
  Next Obligation.
    simpl.
    iIntros (???) "(%&%&%&%&H1) (%&%&%&%&H2)".
    simplify_eq.
    iDestruct (tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "(%&%&%&<-&H1)".
    iPureIntro. rewrite Forall_forall.
    intro. rewrite elem_of_list_filter.
    naive_solver.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????? H1) "Hfrag Herr".
    simplify_eq.
    iMod (state_update_epsilon_err) as "(%ep & %Heps & Heps)".
    iRevert "Hfrag Herr".
    iApply (ec_ind_amp _ (S (S tb))%R with "[][$]"); try lra.
    { 
      pose proof (pos_INR_S (tb)). rewrite S_INR. lra.
    }
    clear ep Heps.
    iModIntro.
    iIntros (eps Heps) "#IH Heps (%&%&%&%&H1) Herr".
    simplify_eq.
    iDestruct (ec_valid with "Herr") as "%".
    iCombine " Herr Heps" as "Herr'".
    iMod (state_update_presample_exp _ _ _ _ _
            (λ x, match decide (fin_to_nat x < S tb)%nat with
                  | left p => ε2 (nat_to_fin p)
                  | _ => ε + S (S tb)*eps
                                  end
            )%R with "[$][$]") as "(%n&Ht&Herr)".
    { intros. case_match; first done.
      apply Rplus_le_le_0_compat; first naive_solver.
      apply Rmult_le_pos; last lra.
      apply pos_INR.
    }
    {
      rewrite !SeriesC_scal_l in H1 *.
      assert (forall (x y z:R), x>0->1/x*y<=z <-> y<=z*x)%R as Hrewrite.
      { intros. rewrite -Rcomplements.Rle_div_l; last done.
        lra. 
      }
      rewrite !Hrewrite in H1 *; [|pose proof pos_INR_S (S tb); lra|pose proof pos_INR_S (tb); lra].
      rewrite !SeriesC_fin_sum in H1 *.
      rewrite -!SeriesC_nat_bounded in H1 *.
      rewrite (SeriesC_split_elem _ (S tb)%fin); last first.
      - apply ex_seriesC_nat_bounded.
      - intros. rewrite /extend_fin_to_R. repeat case_match; try lra.
        + naive_solver.
        + apply Rplus_le_le_0_compat; first lra.
          apply Rmult_le_pos; last lra. apply pos_INR.
      - rewrite SeriesC_singleton_dependent.
        rewrite bool_decide_eq_true_2; last done.
        rewrite /extend_fin_to_R.
        case_match; first lia.
        rewrite fin_to_nat_to_fin. case_match; first lia.
        trans (ε + S (S tb) * eps + ε * S tb)%R; last (rewrite !S_INR; lra).
        assert (SeriesC
                  (λ a : nat,
                     if bool_decide (a ≠ S tb)
                     then
                       if bool_decide (a ≤ S tb)
                       then
                         match le_lt_dec (S (S tb)) a with
                         | left _ => 0
                         | right h =>
                             match decide (nat_to_fin h < S tb)%nat with
                             | left p => ε2 (nat_to_fin p)
                             | right _ => ε + S (S tb) * eps
                             end
                         end
                       else 0
                     else 0) <=ε* S tb)%R; last lra.
        etrans; last exact.
        right.
        apply SeriesC_ext.
        rewrite /extend_fin_to_R.
        intros.
        case_bool_decide as K1; try case_bool_decide as K2; try case_match eqn : K3;
          try rewrite fin_to_nat_to_fin;
          try case_bool_decide as K4; try case_match eqn:K5; try case_match; try (done||lia).
        f_equal.
        apply fin_to_nat_inj.
        by rewrite !fin_to_nat_to_fin.  
    }
    case_match eqn:Hineq.
    - iFrame. iPureIntro. split; first done.
      rewrite filter_app. f_equal. rewrite filter_cons. case_match; try lia.
      by rewrite fin_to_nat_to_fin.
    - iDestruct (ec_split with "[$]") as "[Hε Heps]"; first lra.
      { apply Rmult_le_pos; last lra.
        apply pos_INR.
      } 
      iApply ("IH" with "[$][-Hε][$]").
      iFrame. iPureIntro.
      rewrite filter_app.
      rewrite filter_cons. case_match.
      + simpl in *. lia.
      + by rewrite filter_nil app_nil_r.
  Qed.
  Next Obligation.
    simpl.
    iIntros (? Φ) "_ HΦ".
    wp_pures.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Ht".
    iApply "HΦ". by iFrame.
  Qed.
  Next Obligation.
    iIntros (?? Φ) "AU".
    iApply fupd_pgl_wp.
    iMod "AU" as "(%n &%ns&(%α'&%ns'&%&%Hfilter&Ht)&[AU _])".
    simplify_eq.
    iMod ("AU" with "[$Ht//]") as "AU".
    iModIntro.
    clear.
    iLöb as "IH" forall "AU".
    wp_pures.
    wp_bind (rand(_)_)%E.
    iMod "AU" as "(%&%&(%&%ns'&%&%Hfilter&Ht)&AU)".
    simplify_eq.
    destruct ns' as [|n ns'].
    { rewrite filter_nil in Hfilter. simplify_eq. }
    destruct (decide (n=S tb)%nat).
    - (* reject case *)
      iDestruct "AU" as "[AU _]".
      wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
      iMod ("AU" with "[$Htape]") as "AU".
      { iSplit; first done. iPureIntro.
        rewrite filter_cons in Hfilter.
        case_match; [lia|done].
      }
      iModIntro.
      wp_pures.
      case_bool_decide; first lia.
      wp_pure.
      by iApply "IH".
    - (* accept case*)
      iDestruct "AU" as "[_ AU]".
      wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
      iMod ("AU" with "[$Htape]") as "AU".
      { iSplit; first done. iPureIntro.
        rewrite filter_cons in Hfilter.
        case_match; [by simplify_eq|lia].
      }
      iModIntro.
      wp_pures.
      case_bool_decide; last lia.
      wp_pure.
      rewrite filter_cons in Hfilter.
      case_match; simplify_eq; last lia.
      by iApply "AU".
  Qed.
End impl3.
