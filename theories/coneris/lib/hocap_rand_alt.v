(** * Hocap rand that generates a exclusive token as well
      Useful for building more complex data structures when we need to know all the tapes generated
      We also fix the tape bound
 *)
From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris abstract_tape.

Set Default Proof Using "Type*".

Class rand_spec' (tb:nat) `{!conerisGS Σ} := RandSpec'
{
  (** * Operations *)
  rand_allocate_tape : val;
  rand_tape : val;
  (** * Ghost state *)

  rand_tape_name: Type;
  
  (** * Predicates *)
  is_rand (N:namespace)
    (γ1: rand_tape_name) : iProp Σ; 
  (* rand_tapes_auth {L : randG Σ} (γ: rand_tape_name) (m:gmap loc (nat * list nat)): iProp Σ; *)
  rand_tapes (* (γ: rand_tape_name) *) (α:val) (ns: (list nat)) (γ1: rand_tape_name): iProp Σ;
  rand_token (α: val) (γ:rand_tape_name) : iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_rand_persistent N γ1 ::
    Persistent (is_rand N γ1);
  (* #[global] rand_tapes_auth_timeless {L : randG Σ} γ m :: *)
  (*   Timeless (rand_tapes_auth (L:=L) γ m); *)
  #[global] rand_tapes_timeless α ns γ::
    Timeless (rand_tapes α ns γ);  
  #[global] rand_token_timeless α γ::
    Timeless (rand_token α γ);  
  (* #[global] rand_tape_name_inhabited :: *)
  (*   Inhabited rand_tape_name; *)

  (* rand_tapes_auth_exclusive {L : randG Σ} γ m m': *)
  (* rand_tapes_auth (L:=L) γ m -∗ rand_tapes_auth (L:=L) γ m' -∗ False; *)
  rand_tapes_exclusive α ns ns' γ:
  rand_tapes α ns γ-∗ rand_tapes α ns' γ-∗ False;
  rand_token_exclusive α γ:
  rand_token α γ -∗ rand_token α γ -∗ False; 
  (* rand_tapes_agree {L : randG Σ} γ α m ns: *)
  (* rand_tapes_auth (L:=L) γ m -∗ rand_tapes (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝; *)
  rand_tapes_valid α ns γ:
    rand_tapes α ns γ -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ; 
  (* rand_tapes_update {L : randG Σ} γ α m ns ns': *)
  (* Forall (λ x, x<=ns'.1) ns'.2 -> *)
  (*   rand_tapes_auth (L:=L) γ m -∗ rand_tapes (L:=L) γ α ns ==∗ *)
  (*   rand_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ rand_tapes (L:=L) γ α ns'; *)
  rand_tapes_presample N E α ns ε (ε2 : fin (S tb) -> R) γ:
  ↑N⊆E -> 
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / (S tb) * ε2 n)%R <= ε)%R ->
  is_rand N γ -∗
  rand_tapes α ns γ-∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ rand_tapes α (ns ++ [fin_to_nat n]) γ); 
    

  (** * Program specs *)
  rand_inv_create_spec N E:
  ↑N ⊆ E -> ⊢ |={E}=> (∃ γ1, is_rand N γ1);
  
  rand_allocate_tape_spec N γ E :
  ↑N ⊆ E ->
    {{{ is_rand N γ }}}
      rand_allocate_tape #() @ E
      {{{ (v:val), RET v;
          rand_token v γ∗
           rand_tapes v [] γ
      }}}; 
  
  rand_tape_spec_some N γ E α n ns:
  ↑N ⊆ E ->
    {{{ is_rand N γ ∗ rand_tapes α (n::ns) γ }}}
      rand_tape α @ E
                       {{{ RET #n; rand_tapes α (ns) γ }}}; 
}.

Section impl1.
  Context `{!conerisGS Σ, Hs : !ghost_mapG Σ val (), Hm : !abstract_tapesGS Σ }.
  Variable tb:nat.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Local Definition rand_inv_pred1  (γ:gname*gname) : iProp Σ:=
    (∃ (m:gmap val (list nat)),
        (ghost_map_auth γ.1 1 ((λ _, ())<$>m)) ∗
        ● ((λ x, (tb, x))<$>m)@ γ.2 ∗
        [∗ map] α ↦ns∈m, (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (tb; ns) ))
    )%I.

  Definition is_rand1 N γ:=
    inv N (rand_inv_pred1 γ).

  Definition rand_tapes1 α ns (γ:gname*gname):=
    (α◯↪N (tb; ns) @γ.2 ∗ ⌜Forall (λ x, x<=tb)%nat ns⌝)%I.

  Definition rand_token1 α (γ:gname*gname) :=
    (α ↪[γ.1] ())%I.
  
  #[local] Program Definition rand_spec1 : rand_spec' tb :=
    {| rand_allocate_tape:= (λ: "_", alloc #tb);
      rand_tape:= (λ: "α", rand("α") #tb); 
      is_rand  := is_rand1;
      rand_tapes := rand_tapes1;
      rand_token := rand_token1;
    |}.
  Next Obligation.
    simpl.
    iIntros (????) "[H1 %] [H2 %]".
    iApply (abstract_tapes_frag_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "H1 H2".
    iCombine "H1 H2" gives "%H".
    cbv in H. naive_solver.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???) "(?&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????????) "#Hinv [H1 %] Herr".
    iInv "Hinv" as ">(%&Hs&Hm&Ht)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%Heq&Ht) Hclose']"; first done.
    simplify_eq.
    iMod (state_update_presample_exp with "[$][$]") as "(%n&Ht&Herr)"; [done..|].
    iMod (abstract_tapes_presample with "[$][$]") as "[Hm H1]".
    iDestruct ("Hclose'" with "[$Ht]") as "Ht"; first done.
    iMod ("Hclose" with "[Hs Hm $Ht]"); last iFrame.
    - rewrite !fmap_insert (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome.
    - iPureIntro. apply Forall_app; split; first done.
      apply Forall_singleton. pose proof fin_to_nat_lt n. lia.
  Qed.
  Next Obligation.
    iIntros (???).
    rewrite /is_rand1/rand_inv_pred1.
    iMod (abstract_tapes_alloc ∅) as "(%&H1&_)".
    iMod (ghost_map_alloc_empty) as "(%&H2)".
    iMod (inv_alloc with "[H1 H2]"); last first.
    - iExists (_,_). by iFrame.
    - iNext. iExists ∅.
      rewrite !fmap_empty. by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?[??]?? Φ) "#Hinv HΦ".
    wp_pures.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Ht".
    iAssert (⌜m!!#lbl:α=None⌝)%I as "%Hnone".
    { destruct (_!!_) eqn:?; last done.
      iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
      simplify_eq.
      by iDestruct (tapeN_tapeN_contradict with "[$][$]") as "%".
    }
    iMod (ghost_map_insert with "[$]") as "[Hs Htoken]"; first by erewrite lookup_fmap, Hnone.
    iMod (abstract_tapes_new with "[$]") as "[Hm ?]"; first by erewrite lookup_fmap, Hnone.
    iMod ("Hclose" with "[Hts Ht Hs Hm]").
    { iNext. iExists (<[_:=_]>_). rewrite !fmap_insert.
      iFrame.
      rewrite big_sepM_insert; last done.
      by iFrame.
    }
    iApply "HΦ". by iFrame.
  Qed.
  Next Obligation.
    iIntros (?[??]???? Hsubset Φ) "[#Hinv [Htfrag %]] HΦ".
    iApply fupd_pgl_wp.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&?). simplify_eq.
    iDestruct (big_sepM_lookup_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    iMod ("Hclose" with "[-Htfrag HΦ]") as "_"; iFrame.
    { iDestruct ("Hclose'" with "[-]") as "$". by iFrame. }
    iModIntro. wp_pures.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iMod (abstract_tapes_pop with "[$][$]") as "[Hm Htfrag]".
    iDestruct ("Hclose'" with "[$Htape]") as "Htapes"; first done.
    iMod ("Hclose" with "[-HΦ Htfrag]").
    { iFrame. rewrite !fmap_insert. iFrame.
      rewrite (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome. }
    iApply "HΦ". iFrame.
    iPureIntro. by eapply Forall_inv_tail.
  Qed.
End impl1.

Section checks.
  Context `{H: conerisGS Σ, r1:!rand_spec' tb}.
  
  Lemma wp_rand_tape_1 N n ns α γ:
    {{{ is_rand N γ ∗ ▷ rand_tapes α (n :: ns) γ }}}
      rand_tape α 
                       {{{ RET #(LitInt n); rand_tapes α (ns) γ ∗ ⌜n <= tb⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hinv >Hfrag] HΦ".
    iDestruct (rand_tapes_valid with "[$]") as "%H'". 
    wp_apply (rand_tape_spec_some with "[$Hfrag //]"); first exact.
    iIntros.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite Forall_cons in H'. naive_solver.
  Qed.

  Local Opaque enum_uniform_fin_list.

              
  Lemma wp_presample_adv_comp_rand_tape N E α ns (ε1 : R) (ε2 : fin (S tb) -> R) γ:
    ↑N ⊆ E ->
    (∀ n, 0<=ε2 n)%R ->
    (SeriesC (λ n, (1 / (S tb)) * ε2 n)%R <= ε1)%R →
    is_rand N γ -∗
    ▷ rand_tapes α (ns) γ -∗
    ↯ ε1 -∗
    wp_update E (∃ n, ↯ (ε2 n) ∗ rand_tapes α (ns ++[fin_to_nat n]) γ)%I.
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv >Htape Herr".
    iDestruct (ec_valid with "[$]") as "%Hpos'".
    destruct Hpos' as [Hpos' ?].
    iApply wp_update_state_update.
    by iApply (rand_tapes_presample with "[$][$]").
  Qed.
      

End checks.
