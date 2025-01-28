From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris abstract_tape hocap_rand' lib.map lock con_hash_interface0.

Set Default Proof Using "Type*".
(* Concurrent hash impl*)
(* Section lemmas. *)
(*   Context `{!inG Σ (excl_authR natO)}. *)

(*   (* Helpful lemmas *) *)
(*   Lemma ghost_var_alloc b : *)
(*     ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b). *)
(*   Proof. *)
(*     iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]". *)
(*     - by apply excl_auth_valid. *)
(*     - by eauto with iFrame. *)
(*   Qed. *)

(*   Lemma ghost_var_agree γ b c : *)
(*     own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝. *)
(*   Proof. *)
(*     iIntros "Hγ● Hγ◯". *)
(*     by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L. *)
(*   Qed. *)

(*   Lemma ghost_var_update γ b' b c : *)
(*     own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b'). *)
(*   Proof. *)
(*     iIntros "Hγ● Hγ◯". *)
(*     iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]". *)
(*     { by apply excl_auth_update. } *)
(*     done. *)
(*   Qed. *)

(* End lemmas. *)

Section lemmas.
  Context `{!inG Σ (excl_authR (gmapO nat natO))}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

End lemmas.


(* Class con_hashG (Σ:gFunctors) := ConhashG { *)
(*                                      conhashG_tapesG::inG Σ (excl_authR (gmapO nat natO)); *)
(*                                      conhashG_sizeG::inG Σ (excl_authR natO); *)
(*                                      conhashG_conerisG::conerisGS Σ; *)
(*                                      conhashG_rand::@rand_spec Σ conhashG_conerisG; *)
(*                                      conhashG_randG:randG Σ; *)
(*                                      conhashG_hv::@hash_view Σ conhashG_conerisG; *)
(*                                      conhashG_hvG: hvG Σ; *)
(*                                      conhashG_abstract_tapesG::abstract_tapesGS Σ; *)
(*                                      conhashG_lock::lock; *)
(*                                      conhashG_lockG:lockG Σ *)
                                     
(* }. *)
Section con_hash_impl.
  Variable val_size:nat.
  Context `{Hc: conerisGS Σ,
              (* h : @hash_view Σ Hc, Hhv: hvG Σ, *)
                lo:lock, Hl: lockG Σ,
                  (* r: @rand_spec Σ Hc, Hr: randG Σ, *)
                    Hm: inG Σ (excl_authR (gmapO nat natO)),
                      Ht: !abstract_tapesGS Σ,
                        Hr: !rand_spec' val_size
    }.
  
  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
  (* Definition compute_hash_specialized hm : val := *)
  (*   λ: "v" "α", *)
  (*     match: get hm "v" with *)
  (*     | SOME "b" => "b" *)
  (*     | NONE => *)
  (*         let: "b" := (rand_tape "α" #val_size) in *)
  (*         set hm "v" "b";; *)
  (*         "b" *)
  (*     end. *)
  Definition compute_hash : val :=
    λ: "hm" "v" "α",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := rand_tape "α" in
          set "hm" "v" "b";;
          "b"
      end.

  
  Definition compute_con_hash :val:=
    λ: "lhm" "v" "α",
      let, ("l", "hm") := "lhm" in
      acquire "l";;
      let: "output" := compute_hash "hm" "v" "α" in
      release "l";;
      "output".
  
  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      let: "l" := newlock #() in
      compute_con_hash ("l", "hm").

  Definition allocate_tape : val :=
    λ: "_",
      rand_allocate_tape #().


  Definition compute_con_hash_specialized (lhm:val):val:=
    λ: "v" "α",
      let, ("l", "hm") := lhm in
      acquire "l";;
      let: "output" := (compute_hash "hm") "v" "α" in
      release "l";;
      "output".

  Definition hash_tape α t γ:=(rand_tapes α t γ.1 ∗ α ◯↪N ( val_size ; t ) @ γ.2)%I.
  
  Definition hash_tape_auth m γ :=(([∗ set] α∈ dom m, rand_token α γ.1) ∗
                                   ● ((λ x, (val_size, x))<$>m) @ γ.2)%I.
  (* Definition hash_auth m γ := hv_auth (L:=Hhv) m γ. *)
  (* Definition hash_frag k v γ := hv_frag (L:=Hhv) k v γ. *)
  Definition abstract_con_hash (f:val) (l:val) (hm:val)
    (P: gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')} γ γ_tape: iProp Σ :=
    ∃ m m',
      ⌜f=compute_con_hash_specialized (l, hm)%V⌝ ∗
      (* hv_auth (L:=Hhv) m γ1 ∗ *)
      own γ (●E m) ∗
      hash_tape_auth m' γ_tape ∗
      P m m'
  .
  Definition abstract_con_hash_inv N f l hm P {HP: ∀ m m', Timeless (P m m')} γ γ_tape:=
    (inv (N.@"hash") (abstract_con_hash f l hm P γ γ_tape) ∗ is_rand (N.@"rand") γ_tape.1)%I.
  
  Definition concrete_con_hash (hm:val) (m:gmap nat nat) γ : iProp Σ:=
    ∃ (hm':loc), ⌜hm=#hm'⌝ ∗
    map_list hm' ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
    own γ (◯E m).

  Definition concrete_con_hash_inv hm l γ_lock γ:=
    is_lock (L:=Hl) γ_lock l (∃ m, concrete_con_hash hm m γ).
  
  Definition con_hash_inv N f l hm P {HP: ∀ m m', Timeless (P m m')} γ_tape γ_lock:=
    (∃ γ, abstract_con_hash_inv N f l hm P γ γ_tape ∗
           concrete_con_hash_inv hm l γ_lock γ)%I.

  Lemma con_hash_presample N f l hm P {HP: ∀ m m', Timeless (P m m')} γ γ_lock Q
    E  :
    ↑(N.@"hash") ⊆ E ->
    con_hash_inv N f l hm P γ γ_lock -∗
    (∀ m m', P m m'  -∗
             hash_tape_auth m' γ -∗
             state_update (E∖↑(N.@"hash")) (E∖↑(N.@"hash"))
             (∃ m'', P m m'' ∗ hash_tape_auth m'' γ ∗ Q m m' m'')
    ) -∗
    state_update E E (
        ∃ m m' m'', Q m m' m''
      ).
  Proof.
    iIntros (Hsubset) "#Hinv Hvs".
    iDestruct "Hinv" as "(%γ' & #[Hinv1 Hinv'] & #Hinv2)".
    iInv "Hinv1" as ">(%&%&->&Hown&Hauth&HP)" "Hclose".
    iApply (state_update_mono_fupd (E∖↑(N.@"hash"))).
    { apply difference_mono_l. done. }
    iApply fupd_mask_intro.
    { by apply difference_mono_l.  }
    iIntros "Hclose'".
    iMod ("Hvs" with "[$][$]") as "(%&HP&Hauth&HQ)".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[$Hown $HP $Hauth]"); first done.
    by iFrame.
  Qed.
  

  Lemma con_hash_init N P {HP: ∀ m m', Timeless (P m m')} :
    {{{ P ∅ ∅ }}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ_tape γ_lock, con_hash_inv N f l hm P γ_tape γ_lock }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    rewrite /init_hash.
    iApply fupd_pgl_wp.
    iMod (rand_inv_create_spec) as "(%&#Hrand)"; first done.
    iModIntro.
    wp_pures.
    rewrite /con_hash_inv/abstract_con_hash_inv/abstract_con_hash/concrete_con_hash_inv/concrete_con_hash.
    rewrite /init_hash_state.
    iMod (abstract_tapes_alloc) as "(%γ_tape & Htauth &?)".
    wp_apply (wp_init_map with "[$]") as (l) "Hm".
    wp_pures.
    iMod (ghost_var_alloc ∅) as "[%γ2 [Hauth Hfrag]]".
    wp_apply (newlock_spec with "[Hm Hfrag]") as (loc γ_lock) "#Hl"; last first.
    - wp_pures. 
      iMod (inv_alloc with "[Hauth HP Htauth]") as "#Hinv"; last first.
      + rewrite /compute_con_hash. wp_pures.  iApply "HΦ". iExists _, _, (_,_).
        by iFrame "Hinv Hl Hrand".
      + rewrite /compute_con_hash_specialized. iFrame. iSplit; try done. iNext.
        rewrite dom_empty_L. done.
    - by iFrame.
  Qed.

  Lemma con_hash_alloc_tape N f l hm P {HP: ∀ m m', Timeless (P m m')} γ_tape γ_lock Q:
  {{{ con_hash_inv N f l hm P γ_tape γ_lock ∗
      (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ -∗ |={⊤∖↑N}=> P m (<[α:=[]]>m') ∗ Q α)
  }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ_tape ∗ Q α }}}.
  Proof.
    iIntros (Φ) "[(%&#[Hinv1 Hinv1'] & #Hin2)Hvs] HΦ".
    rewrite /allocate_tape.
    wp_pures.
    iApply pgl_wp_fupd.
    wp_apply (rand_allocate_tape_spec with "[//]") as (α) "[Htoken Hrand]"; first done.
    iInv "Hinv1" as ">(%&%&->&Hown&[Htokens Hauth]&HP)" "Hclose".
    iAssert (⌜α∉dom m'⌝)%I as "%".
    { iIntros "%H".
      rewrite big_sepS_elem_of_acc; last done.
      iDestruct "Htokens" as "[? ?]".
      iApply (rand_token_exclusive with "[$][$]").
    }
    iMod (fupd_mask_subseteq) as "Hclose'"; last iMod ("Hvs" with "[$HP][//]") as "[HP HQ]".
    { apply difference_mono_l. apply nclose_subseteq. }
    iMod "Hclose'" as "_".
    iMod (abstract_tapes_new with "[$]") as "[Hauth Htape]"; last first.
    - iMod ("Hclose" with "[$Hown $HP Hauth Htoken Htokens]").
      + rewrite /hash_tape_auth. rewrite fmap_insert. iFrame.
        iSplit; first done.
        rewrite dom_insert_L big_sepS_insert; last done.
        iFrame.
      + iApply "HΦ". by iFrame.
    - rewrite lookup_fmap. apply not_elem_of_dom_1 in H. by rewrite H.
  Qed.

  Lemma con_hash_spec N f l hm P {HP: ∀ m m', Timeless (P m m')} γ_tape γ_lock Q1 Q2 α ns (v:nat):
  {{{ con_hash_inv N f l hm P γ_tape γ_lock ∗ hash_tape α (ns) γ_tape∗
      ( ∀ m m', P m m' -∗ ⌜m'!!α=Some ns⌝ -∗ |={⊤∖↑N}=>
             match m!!v with
             | Some res => P m m' ∗ Q1 res
             | None => ∃ n ns', ⌜n::ns'=ns⌝ ∗ P (<[v:=n]> m) (<[α:=ns']> m') ∗ Q2
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (hash_tape α (ns) γ_tape ∗ Q1 res ∨
                                 ∃ n ns', ⌜n::ns'=ns⌝ ∗ hash_tape α ns' γ_tape ∗ ⌜res=n⌝ ∗ Q2 
                                )
      }}}.
  Proof.
    iIntros (Φ) "((%&#[Hinv1 Hinv1'] & #Hin2)& [Htape Htape'] & Hvs) HΦ".
    rewrite /abstract_con_hash_inv/concrete_con_hash_inv.
    iApply fupd_pgl_wp.
    iInv "Hinv1" as ">(%&%&->&H1&H2)" "Hclose".
    iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
    iModIntro.
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hin2") as "[Hl[% (%&->&Hm&Hfrag)]]".
    wp_pures.
    rewrite /compute_hash.
    wp_pures.
    wp_apply (wp_get with "[$]") as (res) "[Hm ->]".
    rewrite lookup_fmap.
    destruct (_!!_) eqn:Hres; simpl.
    - (* hashed before *)
      wp_pures.
      iApply fupd_pgl_wp.
      iInv "Hinv1" as ">(%&%&->&H1&[Htapes Htauth]&H2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      rewrite /hash_tape /hash_tape_auth.
      iDestruct (abstract_tapes_agree with "[$][$]") as "%H".
      rewrite lookup_fmap in H. apply fmap_Some_1 in H.
      destruct H as (?&?&?). simplify_eq.
      iMod (fupd_mask_subseteq) as "Hclose'"; last iMod ("Hvs" with "[$][]") as "Hvs"; try done.
      { apply difference_mono_l. apply nclose_subseteq. }
      iMod "Hclose'" as "_".
      rewrite Hres.
      iDestruct "Hvs" as "[HP HQ]".
      iMod ("Hclose" with "[$H1 $HP $Htauth $Htapes]") as "_"; first done.
      iModIntro.
      wp_apply (release_spec with "[$Hin2 $Hl $Hfrag $Hm]") as "_"; first done.
      wp_pures.
      iModIntro. iApply "HΦ".
      iLeft.
      by iFrame.
    - wp_pures.
      rewrite /hash_tape.
      destruct ns eqn : Hns.
      { iApply fupd_pgl_wp.
        iInv "Hinv1" as ">(%&%&->&H1&[Htapes Htauth]&H2)" "Hclose".
        iDestruct (ghost_var_agree with "[$][$]") as "->".
        rewrite /hash_tape /hash_tape_auth.
        iDestruct (abstract_tapes_agree with "[$][$]") as "%H".
        rewrite lookup_fmap in H. apply fmap_Some_1 in H.
        destruct H as (?&?&?). simplify_eq.
        simplify_eq.
        iMod (fupd_mask_subseteq) as "Hclose'"; last iMod ("Hvs" with "[$][]") as "Hvs"; try done.
        { apply difference_mono_l. apply nclose_subseteq. }
        iMod "Hclose'" as "_".
        rewrite Hres.
        iDestruct "Hvs" as "(%&%&%&?)". simplify_eq.
      }
      wp_apply (rand_tape_spec_some with "[$]") as "Htape"; first done.
      iApply fupd_pgl_wp.
      iInv "Hinv1" as ">(%&%&_&Hown&[Htoken Hauth]&HP)" "Hclose".
      iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
      apply lookup_fmap_Some in Hsome.
      destruct Hsome as (?&?&Hsome). simplify_eq.
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iMod (abstract_tapes_pop with "[$][$]") as "[Hauth Htape']".
      simplify_eq.
      iMod (fupd_mask_subseteq) as "Hclose'"; last iMod ("Hvs" with "[$][]") as "Hvs"; try done.
      { apply difference_mono_l. apply nclose_subseteq. }
      iMod "Hclose'" as "_".
      rewrite Hres.
      iDestruct "Hvs" as "(%&%&%&HP&HQ)". simplify_eq.
      iMod (ghost_var_update with "[$][$]") as "[Hown Hown']".
      iMod ("Hclose" with "[Hauth Htoken Hown HP]") as "_".
      { iExists _, (<[_:=_]>_).
        iFrame.
        iSplit; first done.
        rewrite /hash_tape_auth.
        rewrite fmap_insert. iFrame.
        rewrite dom_insert_L subseteq_union_1_L; first done.
        apply elem_of_subseteq_singleton. rewrite elem_of_dom.
        by rewrite Hsome.
      }
      (* iDestruct (abstract_tapes_agree with "[$][$]") as "%H". *)
      (* rewrite lookup_fmap in H. apply fmap_Some_1 in H. *)
      (* destruct H as (?&?&?). simplify_eq. *)
      (* iDestruct (big_sepM_insert_acc with "[$]") as "[H1 H2]"; first done. *)
      (* iDestruct "H1" as "(%&%&H1)". simplify_eq. *)
      (* wp_apply (wp_rand_tape with "[$]") as "[H1 %]". *)
      (* iDestruct ("H2" with "[H1]") as "H2"; first by iFrame. *)
      (* iMod (abstract_tapes_pop with "[$][$]") as "[Hauth Htape]". *)
      (* iDestruct (ghost_var_agree with "[$][$]") as "->". *)
      (* iMod ("Hvs" with "[$HP][//]") as "Hvs". *)
      (* rewrite Hres. *)
      (* iDestruct "Hvs" as "(%&%&%&HP&HQ)". *)
      (* simplify_eq. *)
      (* iMod (ghost_var_update with "[$][$]") as "[Hown Hfrag]". *)
      (* iMod ("Hclose" with "[$Hown $HP Hauth $H2]") as "_". *)
      (* { iSplit; first done. *)
      (*   by rewrite fmap_insert.  *)
      (* } *)
      (* iModIntro. *)
      iModIntro.
      wp_pures.
      wp_apply (wp_set with "[$]") as "Hm".
      wp_pures.
      wp_apply (release_spec with "[$Hin2 $Hown' Hm $Hl]") as "_".
      { iExists _. iSplit; first done. by rewrite fmap_insert. }
      wp_pures.
      iApply "HΦ".
      iFrame. iRight. iFrame. iModIntro.
      iExists _; by repeat iSplit.
  Qed.
    


  Program Definition con_hash_impl0 : con_hash0 val_size :=
    {| init_hash0:=init_hash;
      allocate_tape0:=allocate_tape;
      compute_hash0:=compute_hash;

      hash_tape_gname:=_;
      hash_lock_gname:=_; 
      con_hash_inv0 := con_hash_inv;
      hash_tape0:=hash_tape;
      con_hash_presample0 := con_hash_presample;
      con_hash_init0 := con_hash_init;
      con_hash_alloc_tape0 := con_hash_alloc_tape;
      con_hash_spec0 := con_hash_spec;
    |}
  .
  Next Obligation.
    iIntros (???) "[? ?]".
    by iApply (rand_tapes_valid).
  Qed.
  Next Obligation.
    iIntros (????) "[H1 ?] [H2 ?]".
    iApply (abstract_tapes_frag_exclusive with "[$][$]").
  Qed.
  (* Next Obligation. *)
  (*   iIntros (???) "[??][??]". *)
  (*   iApply (abstract_tapes_auth_exclusive with "[$][$]"). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (????) "[??][??]". *)
  (*   iDestruct (abstract_tapes_agree with "[$][$]") as "%H". *)
  (*   rewrite lookup_fmap in H. apply fmap_Some_1 in H. *)
  (*   destruct H as (?&?&?). by simplify_eq. *)
  (* Qed. *)
  Next Obligation.
    iIntros (?????????????????) "#(%&[? Hinv]&?)[??][??]Herr".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%H'".
    rewrite lookup_fmap in H'. apply fmap_Some_1 in H'.
    destruct H' as (?&Hsome&?). simplify_eq.
    iMod (rand_tapes_presample with "[$][$][$]") as "(%&Htape&?)"; try done.
    (* iDestruct (big_sepM_insert_acc with "[$]") as "[H1 H2]"; first done. *)
    (* iDestruct "H1" as "(%&->&Htape)". *)
    (* (** should have better lemma for this*) *)
    (* iMod (state_update_presample_exp with "[$][$]") as "(%&Htape&?)"; [done..|]. *)
    iMod (abstract_tapes_presample with "[$][$]") as "[? H]".
    iFrame. iModIntro.
    rewrite /hash_tape_auth.
    rewrite fmap_insert. iFrame.
    rewrite dom_insert_L subseteq_union_1_L; first done.
    apply elem_of_subseteq_singleton. rewrite elem_of_dom.
    by rewrite Hsome.
  Qed.
    
    
    
    
  
  (* Definition tape_m_elements (tape_m : gmap val (list nat)) := *)
  (*   concat (map_to_list tape_m).*2. *)
  
  (* Definition abstract_con_hash (f:val) (l:val) (hm:loc) γ1 γ2 γ3 γ4 : iProp Σ := *)
  (*   ∃ m tape_m , *)
  (*     ⌜f=compute_con_hash_specialized (l, #hm)%V⌝ ∗ *)
  (*     ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝ ∗ *)
  (*     (* the tapes*) *)
  (*     ● ((λ x, (val_size, x))<$>tape_m) @ γ1 ∗ *)
  (*     ([∗ map] α ↦ t ∈ tape_m,  rand_tapes (L:=conhashG_randG) α (val_size, t)) ∗ *)
  (*     hv_auth (L:=conhashG_hvG) m γ2 ∗ *)
  (*     ⌜NoDup (tape_m_elements tape_m ++ (map_to_list m).*2)⌝ ∗ *)
  (*     own γ3 (●E m) ∗ *)
  (*     own γ4 (●E (length (map_to_list m) + length (tape_m_elements tape_m))) *)
  (* . *)

  (* Definition abstract_con_hash_inv f l hm γ1 γ2 γ3 γ4:= *)
  (*   inv (nroot.@"con_hash_abstract") (abstract_con_hash f l hm γ1 γ2 γ3 γ4). *)

  (* Definition concrete_con_hash (hm:loc) (m:gmap nat nat) γ : iProp Σ:= *)
  (*   map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗ *)
  (*   own γ (◯E m). *)

  (* Definition concrete_con_hash_inv hm l γ_lock γ:= *)
  (*   is_lock (L:=conhashG_lockG) γ_lock l (∃ m, concrete_con_hash hm m γ). *)

  (* Definition con_hash_inv f l hm γ1 γ2 γ3 γ4 γ_lock := *)
  (*   (abstract_con_hash_inv f l hm γ1 γ2 γ3 γ4 ∗ *)
  (*   concrete_con_hash_inv hm l γ_lock γ3)%I. *)

End con_hash_impl.


  (* Lemma con_hash_spec' N f l hm γ1 γlock α n ns (v:nat): *)
  (*   {{{ con_hash_inv N f l hm γ1 γlock ∗ hash_tape α (n::ns) }}} *)
  (*     f #v α *)
  (*     {{{ (res:nat), RET (#res);  hash_frag v res γ1 ∗ *)
  (*                               (hash_tape α ns ∗ ⌜res=n⌝ ∨ *)
  (*                                hash_tape α (n::ns) *)
  (*                               ) *)
  (*     }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "[[#Hab #Hcon]Ht] HΦ". *)
  (*   rewrite /abstract_con_hash_inv/concrete_con_hash_inv. *)
  (*   iApply fupd_pgl_wp. *)
  (*   iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*   iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*   iModIntro. *)
  (*   rewrite /compute_con_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]". *)
  (*   wp_pures. *)
  (*   rewrite /compute_hash. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]") as (res) "[Hm ->]". *)
  (*   rewrite lookup_fmap. *)
  (*   destruct (_!!_) eqn:Hres; simpl. *)
  (*   - (* hashed before *) *)
  (*     wp_pures. *)
  (*     iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iMod (hv_auth_duplicate_frag with "[$]") as "[H1 Hfrag']"; first done. *)
  (*     iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*     iModIntro. *)
  (*     wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done. *)
  (*     wp_pures. *)
  (*     iModIntro. iApply "HΦ". *)
  (*     iFrame. *)
  (*   - wp_pures. *)
  (*     rewrite /hash_tape. *)
  (*     wp_apply (rand_tape_spec_some with "[$]") as "Ht". *)
  (*     wp_pures. *)
  (*     wp_apply (wp_set with "[$]") as "Hm". *)
  (*     iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iMod (ghost_var_update _ (<[v:=n]> _) with "[$][$]") as "[H2 Hfrag]". *)
  (*     iMod (hv_auth_insert with "[$]") as "[H1 Hfrag']"; first done. *)
  (*     iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*     iModIntro. *)
  (*     wp_pures. *)
  (*     wp_apply (release_spec with "[$Hl $Hcon $Hfrag Hm]") as "_". *)
  (*     { iExists _. iSplit; first done. by rewrite fmap_insert. } *)
  (*     wp_pures. *)
  (*     iApply "HΦ". *)
  (*     iFrame. iLeft. by iFrame. *)
  (* Qed. *)

  (* Lemma con_hash_spec_hashed_before f l hm γ1 γ2 γlock α ns res (v:nat): *)
  (*   {{{ con_hash_inv f l hm γ1 γ2 γlock ∗ hash_tape α ns ∗ hash_frag v res γ1}}} *)
  (*     f #v α *)
  (*     {{{ RET (#res);  hash_frag v res γ1 ∗ *)
  (*                      (hash_tape α ns) *)
  (*     }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "[[#Hab #Hcon][Ht #Hfragv]] HΦ". *)
  (*   rewrite /abstract_con_hash_inv/concrete_con_hash_inv. *)
  (*   iApply fupd_pgl_wp. *)
  (*   iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*   iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*   iModIntro. *)
  (*   rewrite /compute_con_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]". *)
  (*   wp_pures. *)
  (*   rewrite /compute_hash. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]") as (res') "[Hm ->]". *)
  (*   rewrite lookup_fmap. *)
  (*   destruct (_!!_) eqn:Hres; simpl. *)
  (*   - (* hashed before *) *)
  (*     wp_pures. *)
  (*     iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iDestruct (hv_auth_frag_agree with "[$]") as "%H". *)
  (*     rewrite Hres in H. simplify_eq. *)
  (*     iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*     iModIntro. *)
  (*     wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done. *)
  (*     wp_pures. iModIntro. *)
  (*     iApply "HΦ". *)
  (*     iFrame. iExact "Hfragv". *)
  (*   - iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iDestruct (hv_auth_frag_agree with "[$]") as "%H". simplify_eq. *)
  (* Qed. *)
  
