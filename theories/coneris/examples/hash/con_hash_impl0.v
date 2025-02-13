From iris.algebra Require Import gmap.
From clutch.coneris Require Import coneris hocap_rand_alt lib.map lock con_hash_interface0.

Set Default Proof Using "Type*".
(* Concurrent hash impl*)
(* Section lemmas. *)
(*   Context `{!inG Σ (excl_authR (gmapO nat natO))}. *)

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


Section con_hash_impl.
  Variable val_size:nat.
  Context `{Hc: conerisGS Σ,
              (* h : @hash_view Σ Hc, Hhv: hvG Σ, *)
                lo:lock, Hl: lockG Σ,
                    (* Hm: inG Σ (excl_authR (gmapO nat natO)), *)
                    (*   Ht: !abstract_tapesGS Σ, *)
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

  Definition hash_tape α t γ:=(rand_tapes α t γ)%I.
  
  (* Definition hash_tape_auth m γ :=(([∗ set] α∈ dom m, rand_token α γ.1) ∗ *)
  (*                                  ● ((λ x, (val_size, x))<$>m) @ γ.2)%I. *)
  Definition abstract_con_hash (f:val) (l:val) (hm:val): iProp Σ :=
      ⌜f=compute_con_hash_specialized (l, hm)%V⌝ 
  .
  Definition abstract_con_hash_inv N f l hm γ_tape:=
    ((abstract_con_hash f l hm) ∗ is_rand (N) γ_tape)%I.
  
  Definition concrete_con_hash (hm:val) (m:gmap nat nat) R {HR: ∀ m, Timeless (R m )} : iProp Σ:=
    ∃ (hm':loc), ⌜hm=#hm'⌝ ∗
    map_list hm' ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
    R m
  .

  Definition concrete_con_hash_inv hm l R {HR: ∀ m, Timeless (R m )} γ_lock:=
    is_lock (L:=Hl) γ_lock l (∃ m, concrete_con_hash hm m R).
  
  Definition con_hash_inv N f l hm R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock:=
    (abstract_con_hash_inv N f l hm γ_tape ∗
           concrete_con_hash_inv hm l R γ_lock)%I.

  Lemma con_hash_tape_presample N γ γ_lock f l hm R {HR: ∀ m, Timeless (R m )} α ns ε ε2 E:
  ↑(N)⊆E ->
    (∀ x : fin (S val_size), (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    con_hash_inv N f l hm R γ γ_lock -∗
    hash_tape α ns γ -∗ ↯ ε -∗
    state_update E E (∃ n, 
          ↯ (ε2 n) ∗
          hash_tape α (ns++[fin_to_nat n]) γ).
  Proof.
    iIntros (Hsubset Hpos Hineq) "#([->?]&?)?Herr".
    iMod (rand_tapes_presample with "[$][$][$]") as "(%&Htape&?)"; try done.
    (* iDestruct (big_sepM_insert_acc with "[$]") as "[H1 H2]"; first done. *)
    (* iDestruct "H1" as "(%&->&Htape)". *)
    (* (** should have better lemma for this*) *)
    (* iMod (state_update_presample_exp with "[$][$]") as "(%&Htape&?)"; [done..|]. *)
    by iFrame. 
  Qed.
  

  Lemma con_hash_init N R {HR: ∀ m, Timeless (R m )} :
    {{{ R ∅}}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ_tape γ_lock, con_hash_inv N f l hm R γ_tape γ_lock }}}.
  Proof.
    iIntros (Φ) "HR HΦ".
    rewrite /init_hash.
    iApply fupd_pgl_wp.
    iMod (rand_inv_create_spec) as "(%&#Hrand)"; first done.
    iModIntro.
    wp_pures.
    rewrite /con_hash_inv/abstract_con_hash_inv/abstract_con_hash/concrete_con_hash_inv/concrete_con_hash.
    rewrite /init_hash_state.
    wp_apply (wp_init_map with "[$]") as (l) "Hm".
    wp_pures.
    wp_apply (newlock_spec with "[Hm HR]") as (loc γ_lock) "#Hl"; last first.
    - wp_pures. 
      rewrite /compute_con_hash. wp_pures.  iApply "HΦ". iModIntro.
      by iFrame "Hl Hrand".
    - by iFrame.
  Qed.

  Lemma con_hash_alloc_tape N f l hm R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock:
  {{{ con_hash_inv N f l hm R γ_tape γ_lock 
  }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ_tape }}}.
  Proof.
    iIntros (Φ) "(#[-> Hinv1'] & #Hin2) HΦ".
    rewrite /allocate_tape.
    wp_pures.
    wp_apply (rand_allocate_tape_spec with "[//]") as (α) "[_ Hrand]"; first done.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma con_hash_spec N f l hm R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv N f l hm R γ_tape γ_lock ∗ 
      ( ∀ m , R m -∗ state_update (⊤) (⊤)
             match m!!v with
             | Some res => R m ∗ Q1 res
             | None => ∃ n ns, hash_tape α (n::ns) γ_tape ∗ 
                              (hash_tape α (ns) γ_tape ={⊤}=∗ R (<[v:=n]> m) ∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns, Q2 res ns
                                )
      }}}.
  Proof.
    iIntros (Φ) "((#[-> Hinv1'] & #Hin2) & Hvs) HΦ".
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hin2") as "[Hl[% (%&->&Hm&HR)]]".
    wp_pures.
    rewrite /compute_hash.
    wp_pures.
    wp_apply (wp_get with "[$]") as (res) "[Hm ->]".
    rewrite lookup_fmap.
    destruct (_!!_) eqn:Hres; simpl.
    - (* hashed before *)
      wp_pures.
      iApply state_update_pgl_wp.
      iMod ("Hvs" with "[$]") as "Hvs"; try done.
      rewrite Hres.
      iDestruct "Hvs" as "(HR & HQ)".
      iModIntro.
      wp_apply (release_spec with "[$Hin2 $Hl $Hm $HR]") as "_"; first done.
      wp_pures.
      iModIntro. iApply "HΦ".
      iLeft.
      by iFrame.
    - wp_pures.
      rewrite /hash_tape.
      (* destruct ns eqn : Hns. *)
      (* { iApply fupd_pgl_wp. *)
      (*   iInv "Hinv1" as ">(%&%&->&H1&[Htapes Htauth]&H2)" "Hclose". *)
      (*   iDestruct (ghost_var_agree with "[$][$]") as "->". *)
      (*   rewrite /hash_tape /hash_tape_auth. *)
      (*   iDestruct (abstract_tapes_agree with "[$][$]") as "%H". *)
      (*   rewrite lookup_fmap in H. apply fmap_Some_1 in H. *)
      (*   destruct H as (?&?&?). simplify_eq. *)
      (*   simplify_eq. *)
      (*   iMod (fupd_mask_subseteq) as "Hclose'"; last iMod ("Hvs" with "[$][$][]") as "Hvs"; try done. *)
      (*   { apply difference_mono_l. apply nclose_subseteq. } *)
      (*   iMod "Hclose'" as "_". *)
      (*   rewrite Hres. *)
      (*   iDestruct "Hvs" as "(%&%&%&?)". simplify_eq. *)
      (* } *)
      iApply state_update_pgl_wp.
      rewrite /hash_tape.
      iMod ("Hvs" with "[$]") as "Hvs"; try done.
      rewrite Hres.
      iDestruct "Hvs" as "(%&%& Htape&Hvs)".
      iModIntro.
      wp_apply (rand_tape_spec_some with "[$]") as "Htape"; first done.
      iMod ("Hvs" with "[$]") as "Hvs"; try done.
      iDestruct "Hvs" as "(HR&HQ)". 
      wp_pures.
      wp_apply (wp_set with "[$]") as "Hm".
      wp_pures.
      wp_apply (release_spec with "[$Hin2 $HR Hm $Hl]") as "_".
      { iExists _. iSplit; first done. by rewrite fmap_insert. }
      wp_pures.
      iApply "HΦ".
      by iFrame. 
  Qed.
    


  Program Definition con_hash_impl0 : con_hash0 val_size :=
    {| init_hash0:=init_hash;
      allocate_tape0:=allocate_tape;
      compute_hash0:=compute_hash;

      hash_tape_gname:=_;
      hash_lock_gname:=_; 
      con_hash_inv0 := con_hash_inv;
      hash_tape0:=hash_tape;
      hash_tape_presample := con_hash_tape_presample;
      con_hash_init0 := con_hash_init;
      con_hash_alloc_tape0 := con_hash_alloc_tape;
      con_hash_spec0 := con_hash_spec;
    |}
  .
  Next Obligation.
    iIntros (???) " ?".
    by iApply (rand_tapes_valid).
  Qed.
  Next Obligation.
    iIntros (????) "H1 H2".
    iApply (rand_tapes_exclusive with "[$][$]").
  Qed.
  (* Next Obligation. *)
  (*   iIntros (???) "[??][??]". *)
  (*   iApply (abstract_tapes_auth_exclusive with "[$][$]"). *)
  (* Qed. *)
    
    
    
  
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
  
