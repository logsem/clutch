From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris hocap_rand lib.map hash_view_interface lock con_hash_interface0.

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
  Context `{Hc: conerisGS Σ,
              h : @hash_view Σ Hc, Hhv: hvG Σ,
                lo:lock, Hl: lockG Σ,
                  r: @rand_spec Σ Hc, Hr: randG Σ,
                    Hm: inG Σ (excl_authR (gmapO nat natO))
    }.
  Variable val_size:nat.
  
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
          let: "b" := (rand_tape "α" #val_size) in
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
      rand_allocate_tape #val_size.


  Definition compute_con_hash_specialized (lhm:val):val:=
    λ: "v" "α",
      let, ("l", "hm") := lhm in
      acquire "l";;
      let: "output" := (compute_hash "hm") "v" "α" in
      release "l";;
      "output".

  Definition hash_tape α t:=rand_tapes (L:=Hr) α (val_size, t).
  Definition con_hash_view k v γ := hv_frag (L:=Hhv) k v γ.
  Definition abstract_con_hash (f:val) (l:val) (hm:val) γ1 γ2 : iProp Σ :=
    ∃ m,
      ⌜f=compute_con_hash_specialized (l, hm)%V⌝ ∗
      hv_auth (L:=Hhv) m γ1 ∗
      own γ2 (●E m) 
  .
  Definition abstract_con_hash_inv f l hm γ1 γ2:=
    inv (nroot.@"con_hash_abstract") (abstract_con_hash f l hm γ1 γ2).
  
  Definition concrete_con_hash (hm:val) (m:gmap nat nat) γ : iProp Σ:=
    ∃ (hm':loc), ⌜hm=#hm'⌝ ∗
    map_list hm' ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
    own γ (◯E m).

  Definition concrete_con_hash_inv hm l γ_lock γ:=
    is_lock (L:=Hl) γ_lock l (∃ m, concrete_con_hash hm m γ).
  
  Definition con_hash_inv f l hm γ1 γ2 γ_lock:=
    (abstract_con_hash_inv f l hm γ1 γ2  ∗
     concrete_con_hash_inv hm l γ_lock γ2)%I.

  Lemma con_hash_presample E (ε:nonnegreal) ns α (ε2 : fin (S val_size) → R):
    (∀ x : fin (S val_size), (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    hash_tape α ns -∗
    ↯ ε -∗
    state_update E E (∃ n,
          ↯ (ε2 n) ∗
          hash_tape α (ns++[fin_to_nat n]) 
      ).
  Proof.
    iIntros (Hineq Hpos) "Ht Herr".
    rewrite /hash_tape.
    iMod (rand_tapes_presample with "[$][$]"); [done..|].
    by iFrame.
  Qed.

  Lemma con_hash_init:
    {{{ True }}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ_lock, con_hash_inv f l hm γ1 γ2 γ_lock }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_hash.
    wp_pures.
    rewrite /con_hash_inv/abstract_con_hash_inv/abstract_con_hash/concrete_con_hash_inv/concrete_con_hash.
    rewrite /init_hash_state.
    wp_apply (wp_init_map with "[$]") as (l) "Hm".
    wp_pures.
    iMod (ghost_var_alloc ∅) as "[%γ2 [Hauth Hfrag]]".
    wp_apply (newlock_spec with "[Hm Hfrag]") as (loc γ_lock) "#Hl"; last first.
    - wp_pures. 
      iMod hv_auth_init as "[%γ1 Hv]".
      iMod (inv_alloc with "[Hauth Hv]") as "#Hinv"; last first.
      + rewrite /compute_con_hash. wp_pures.  iApply "HΦ". by iFrame "Hinv Hl".
      + rewrite /compute_con_hash_specialized. by iFrame.
    - by iFrame.
  Qed.

  Lemma con_hash_alloc_tape:
    {{{ True }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /allocate_tape.
    wp_pures.
    wp_apply (rand_allocate_tape_spec with "[//]") as (v) "?".
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma con_hash_spec f l hm γ1 γ2 γlock α n ns (v:nat):
    {{{ con_hash_inv f l hm γ1 γ2 γlock ∗ hash_tape α (n::ns) }}}
      f #v α
      {{{ (res:nat), RET (#res);  con_hash_view v res γ1 ∗
                                (hash_tape α ns ∗ ⌜res=n⌝ ∨
                                 hash_tape α (n::ns)
                                )
      }}}.
  Proof.
    iIntros (Φ) "[[#Hab #Hcon]Ht] HΦ".
    rewrite /abstract_con_hash_inv/concrete_con_hash_inv.
    iApply fupd_pgl_wp.
    iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
    iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
    iModIntro.
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]".
    wp_pures.
    rewrite /compute_hash.
    wp_pures.
    wp_apply (wp_get with "[$]") as (res) "[Hm ->]".
    rewrite lookup_fmap.
    destruct (_!!_) eqn:Hres; simpl.
    - (* hashed before *)
      wp_pures.
      iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iMod (hv_auth_duplicate_frag with "[$]") as "[H1 Hfrag']"; first done.
      iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
      iModIntro.
      wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done.
      wp_pures.
      iModIntro. iApply "HΦ".
      iFrame.
    - wp_pures.
      rewrite /hash_tape.
      wp_apply (rand_tape_spec_some with "[$]") as "Ht".
      wp_pures.
      wp_apply (wp_set with "[$]") as "Hm".
      iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iMod (ghost_var_update _ (<[v:=n]> _) with "[$][$]") as "[H2 Hfrag]".
      iMod (hv_auth_insert with "[$]") as "[H1 Hfrag']"; first done.
      iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
      iModIntro.
      wp_pures.
      wp_apply (release_spec with "[$Hl $Hcon $Hfrag Hm]") as "_".
      { iExists _. iSplit; first done. by rewrite fmap_insert. }
      wp_pures.
      iApply "HΦ".
      iFrame. iLeft. by iFrame.
  Qed.

  Lemma con_hash_spec_hashed_before f l hm γ1 γ2 γlock α ns res (v:nat):
    {{{ con_hash_inv f l hm γ1 γ2 γlock ∗ hash_tape α ns ∗ con_hash_view v res γ1}}}
      f #v α
      {{{ RET (#res);  con_hash_view v res γ1 ∗
                       (hash_tape α ns)
      }}}.
  Proof.
    iIntros (Φ) "[[#Hab #Hcon][Ht #Hfragv]] HΦ".
    rewrite /abstract_con_hash_inv/concrete_con_hash_inv.
    iApply fupd_pgl_wp.
    iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
    iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
    iModIntro.
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]".
    wp_pures.
    rewrite /compute_hash.
    wp_pures.
    wp_apply (wp_get with "[$]") as (res') "[Hm ->]".
    rewrite lookup_fmap.
    destruct (_!!_) eqn:Hres; simpl.
    - (* hashed before *)
      wp_pures.
      iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iDestruct (hv_auth_frag_agree with "[$]") as "%H".
      rewrite Hres in H. simplify_eq.
      iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
      iModIntro.
      wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done.
      wp_pures. iModIntro.
      iApply "HΦ".
      iFrame. iExact "Hfragv".
    - iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iDestruct (hv_auth_frag_agree with "[$]") as "%H". simplify_eq.
  Qed.
  

  Program Definition con_hash_impl0 : con_hash0 val_size :=
    {| init_hash0:=init_hash;
      allocate_tape0:=allocate_tape;
      compute_hash0:=compute_hash;

      hash_view_gname:=_;
      hash_map_gname:=gname;
      hash_lock_gname:=_;
      con_hash_inv0 := con_hash_inv;
      hash_tape0:=hash_tape;
      con_hash_view0:=con_hash_view;
      con_hash_presample0 := con_hash_presample;
      con_hash_init0 := con_hash_init;
      con_hash_alloc_tape0 := con_hash_alloc_tape;
      con_hash_spec0 := con_hash_spec;
      con_hash_spec_hashed_before0 := con_hash_spec_hashed_before                
    |}
  .
  Next Obligation.
    iIntros.
    rewrite /con_hash_inv.
    by iApply hv_frag_frag_agree.
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

