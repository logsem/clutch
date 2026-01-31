From iris.algebra Require Import gmap.
From clutch.coneris Require Import coneris hocap_rand_alt lock lazy_rand_interface.

Set Default Proof Using "Type*".
Section impl.
  Variable val_size:nat.
  Context `{Hc: conerisGS Σ,
              Hv: !ghost_mapG Σ () (option (nat*nat)),
                lo:lock, Hl: lockG Σ,
                        Hr: !rand_spec' val_size
    }.

  Definition init_lazy_rand_prog : val := λ: "_", let: "x":= ref NONE in
                                             let: "l":=newlock #() in
                                             ("l", "x")
  .
  Definition allocate_tape_prog: val := λ: "_", rand_allocate_tape #().
  Definition lazy_read_rand_prog: val := λ: "r" "α" "tid",
                                 let, ("l", "x"):="r" in
                                 acquire "l";;
                                 let: "val" := (match: ! "x" with
                                                | SOME "x'" =>
                                                    "x'"
                                                | NONE =>
                                                    let: "x'" := (rand_tape "α", "tid") in 
                                                    "x" <- SOME "x'";;
                                                    "x'"
                                                end) in
                                 release "l" ;;
                                 "val"
                                   
  .

  Definition option_to_list (n:option nat):=
    match n with
    | Some (n') => [n']
    | None =>[]
    end.
        
              
  Definition rand_tape_frag α n γ :=
    (rand_tapes α (option_to_list n) γ )%I.
  

  Definition abstract_lazy_rand_inv N γ_tape:=
    ( is_rand (N) γ_tape)%I.


  Definition option_to_gmap n : gmap () (option (nat*nat)):=
    <[():=n]>∅.

  Definition option_valid (n:option (nat* nat)) :=
    match n with
    | Some (n1, n2) => (n1<=val_size)%nat
    | None => True
    end.

  Definition option_to_val (n:option(nat*nat)):val :=
    match n with
    | Some (n1, n2) => SOMEV (#n1, #n2)%V
    | None => NONEV end.     

  Definition rand_frag (res tid:nat) (γ:gname):=(() ↪[γ]□ Some (res, tid) ∗ ⌜res<=val_size⌝)%I.
  
  Definition option_duplicate (n:option (nat* nat)) γ:=
    match n with
    | Some (n1, n2) => rand_frag n1 n2 γ
    | None => (() ↪[γ] None)%I
    end.
  
  Definition rand_auth (n:option (nat*nat)) γ :=
    (ghost_map_auth γ 1 (option_to_gmap n) ∗
     option_duplicate n γ ∗
     ⌜option_valid n⌝)%I.

  
  Definition lazy_rand_inv N c P{HP: ∀ n, Timeless (P n)}  γ_tape γ_view γ_lock :=
    (∃ lk (l:loc),
      ⌜c=(lk, #l)%V⌝ ∗
      abstract_lazy_rand_inv N γ_tape ∗
      is_lock (L:=Hl) γ_lock lk (∃ res, P res ∗ rand_auth res γ_view ∗ l↦(option_to_val res)))%I.

  Lemma rand_tape_presample_impl N c P {HP:∀ n, Timeless (P n)} γ γ_view γ_lock E α ε (ε2:fin (S val_size) -> R):
    ↑(N)⊆E ->
    (∀ x, (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    lazy_rand_inv N c P γ γ_view γ_lock -∗
     rand_tape_frag α None γ -∗ ↯ ε -∗
    state_update E E (∃ n, 
          ↯ (ε2 n) ∗
          rand_tape_frag α (Some (fin_to_nat n)) γ).
  Proof. 
    iIntros (???) "(%&%&->&# Hinv&#?) Htape Herr".
    (* iDestruct (abstract_tapes_agree with "[$][$]") as "%H'". *)
    (* rewrite lookup_fmap in H'. apply fmap_Some_1 in H'. *)
    (* destruct H' as (?&Hsome&?). simplify_eq. *)
    iMod (rand_tapes_presample with "[$][$][$]") as "(%&Htape&?)"; try done.
    (* iMod (abstract_tapes_presample with "[$][$]") as "[? H]". *)
    by iFrame. 
  Qed.

  Lemma lazy_rand_init_impl N P {HP: ∀ n, Timeless (P n)} :
    {{{ P None }}}
      init_lazy_rand_prog #()
      {{{ (c:val), RET c;
          ∃ γ γ_view γ_lock, 
            lazy_rand_inv N c P γ γ_view γ_lock }}}.
  Proof.
    iIntros (Φ) "HP HΦ". iApply pgl_wp_fupd.
    rewrite /init_lazy_rand_prog.
    wp_pures.
    wp_alloc x as "Hx".
    wp_pures.
    iMod (ghost_map_alloc (<[():=None]> ∅)) as "(%&Hm&Ht)".
    wp_apply (newlock_spec (∃ res, P res ∗ rand_auth res _ ∗ _↦(option_to_val res))%I
                           with "[$HP $Hx $Hm Ht]"
             ).
    { simpl. iSplit; last done.
      iDestruct (big_sepM_lookup with "[$]") as "$".
      apply lookup_insert.
    }
    iIntros (??) "#Hlock".
    wp_pures.
    iMod (rand_inv_create_spec) as "(%&#Hrand)"; last first.
    - (* iMod (abstract_tapes_alloc ∅) as "(%&Hm&_)". *)
      (* iMod (inv_alloc _ _ (∃ m, rand_tape_auth m (_,_)) with "[Hm]") as "#Hinv". *)
      (* { iNext. iExists ∅. rewrite /rand_tape_auth. rewrite fmap_empty. *)
      (*   iFrame. by rewrite dom_empty_L. } *)
      iApply "HΦ". iFrame "Hlock".
      rewrite /abstract_lazy_rand_inv. iExists _. 
      by iFrame "Hrand".
    - done.
  Qed.

  Lemma lazy_rand_alloc_tape_impl N c P {HP: ∀ n, Timeless (P n)} γ_tape γ_view γ_lock :
  {{{ lazy_rand_inv N c P γ_tape γ_view γ_lock 
  }}}
      allocate_tape_prog #()
      {{{ (α: val), RET α; rand_tape_frag α None γ_tape  }}}.
  Proof.
    iIntros (Φ) "(%&%&->&#Hinv &_) HΦ".
    rewrite /allocate_tape_prog.
    wp_pures.
    iApply pgl_wp_fupd.
    wp_apply (rand_allocate_tape_spec with "[//]") as (α) "[Htoken Hrand]"; first done.
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma lazy_rand_spec_impl N c P {HP: ∀ n, Timeless (P n)} γ_tape γ_view γ_lock Q1 Q2 α (tid:nat):
  {{{ lazy_rand_inv N c P γ_tape γ_view γ_lock ∗
      ( ∀ n, P n -∗ rand_auth n γ_view -∗ state_update (⊤) (⊤)
             match n with
             | Some (res, tid') => P n ∗ rand_auth n γ_view ∗ Q1 res tid'
             | None => ∃ n', rand_tape_frag α (Some n') γ_tape ∗
                              (rand_tape_frag α None γ_tape
                                      ={⊤}=∗  P (Some (n', tid)) ∗ rand_auth (Some (n', tid)) γ_view ∗ Q2 n' tid)
             end                                        
      )
  }}}
      lazy_read_rand_prog c α #tid 
      {{{ (res' tid':nat), RET (#res', #tid')%V;  (Q1 res' tid' ∨
                                                   Q2 res' tid'
                                )
      }}}.
  Proof.
    iIntros (Φ) "[(%&%&->&#Hinv&#Hlock) Hvs] HΦ".
    rewrite /lazy_read_rand_prog. wp_pures.
    wp_apply (acquire_spec with "[$]") as "[Hl (%res&HP&(Hauth & Hfrag & %Hvalid)&Hloc)]".
    wp_pures.
    wp_load.
    iApply state_update_pgl_wp.
    (* iInv ("Hinv") as ">(%&Htokens&Htauth)" "Hclose". *)
    iMod ("Hvs" with "[$][$Hauth $Hfrag//]") as "Hcont".
    destruct res as [[]|].
    - iDestruct "Hcont" as "(HP&Hauth &HQ)".
      iModIntro. wp_pures.
      wp_apply (release_spec with "[$Hlock $Hl $HP $Hloc $Hauth]").
      iIntros. wp_pures.
      iApply "HΦ". by iFrame.
    - iDestruct "Hcont" as "(%&Ht  & Hvs)".
      (* iMod ("Hclose" with "[$Htauth $Htokens]") as "_". *)
      iModIntro. wp_pures.
      wp_apply (rand_tape_spec_some with "[$]") as "Htape"; first done.
      iApply fupd_pgl_wp.
      (* iInv ("Hinv") as ">(%&Htokens&Htauth)" "Hclose". *)
      (* iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome". *)
      (* apply lookup_fmap_Some in Hsome. *)
      (* destruct Hsome as ([x|]&?&Hsome); simplify_eq. *)
      (* iMod (abstract_tapes_pop with "[$][$]") as "[Hauth Htape']". *)
      iMod ("Hvs" with "[$]") as "(HP&Hrand&HQ)".
      (* iMod ("Hclose" with "[Hauth Htokens]") as "_". *)
      (* { iExists (<[_:=None]>_). *)
      (*   rewrite /rand_tape_auth. rewrite fmap_insert. *)
      (*   rewrite dom_insert_lookup_L; last done. iFrame. *)
      (* } *)
      iModIntro.
      wp_pures.
      wp_store.
      wp_pures.
      wp_apply (release_spec with "[$Hlock $Hl $HP $Hloc $Hrand]").
      iIntros. wp_pures. iModIntro. iApply "HΦ".
      iFrame.
  Qed.
  
  Program Definition lazy_rand_impl : lazy_rand val_size :=
    {| init_lazy_rand := init_lazy_rand_prog;
      allocate_tape := allocate_tape_prog;
      lazy_read_rand := lazy_read_rand_prog;
      lazy_rand_interface.rand_tape_frag := rand_tape_frag;
      (* lazy_rand_interface.rand_tape_auth := rand_tape_auth; *)
      lazy_rand_interface.rand_auth := rand_auth;
      lazy_rand_interface.rand_frag := rand_frag;
      rand_inv:=lazy_rand_inv;
      rand_tape_presample:=rand_tape_presample_impl;
      (* lazy_rand_presample:=lazy_rand_presample_impl; *)
      lazy_rand_init:=lazy_rand_init_impl;
      lazy_rand_alloc_tape:=lazy_rand_alloc_tape_impl;
      lazy_rand_spec:=lazy_rand_spec_impl
    |}
  .
  (* Next Obligation. *)
  (*   intros ???. *)
  (*   intros [[]|]?; rewrite /rand_auth/=; apply _. *)
  (* Qed. *)
  Next Obligation.
    rewrite /rand_tape_frag/=.
    iIntros (???) "?".
    iDestruct (rand_tapes_valid with "[$]") as "%H".
    by rewrite Forall_singleton in H.
  Qed.
  Next Obligation.
    rewrite /rand_tape_frag.
    iIntros (????) "??".
    iApply (rand_tapes_exclusive with "[$][$]").
  Qed.
  (* Next Obligation. *)
  (*   rewrite /rand_tape_auth/rand_tape_frag. *)
  (*   iIntros (?? x ?) "[??][??]". *)
  (*   iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome". *)
  (*   apply lookup_fmap_Some in Hsome. *)
  (*   by destruct Hsome as ([[]|]&?&Hsome); destruct x; simplify_eq. *)
  (* Qed. *)
  Next Obligation.
    rewrite /rand_auth.
    iIntros (???) "[??][??]".
    iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%?]".
    done.
  Qed.
  Next Obligation.
    rewrite /rand_auth/rand_frag.
    iIntros (????)"[H ?][H' ?]".
    iCombine "H H'" gives "%H".
    destruct n; simpl in H; simplify_eq.
    rewrite /option_to_gmap in H. rewrite lookup_insert in H.
    by simplify_eq.
  Qed.
  Next Obligation.
    iIntros ([]?) "(?&#?&?)".
    by done. 
  Qed.
  Next Obligation.
    iIntros (???) "(?&?&%)".
    done.
  Qed.
  Next Obligation.
    iIntros (???) "[??]".
    done.
  Qed.
  Next Obligation.
    rewrite /rand_frag.
    iIntros (?????) "[H ?] [H' ?]".
    iCombine "H H'" gives "%".
    iPureIntro. naive_solver.
  Qed.
  Next Obligation.
    rewrite /rand_auth /=.
    iIntros ([??]??) "(?&?&_)".
    rewrite /option_to_gmap/=.
    iMod (ghost_map_update with "[$][$]") as "[??]". rewrite insert_insert.
    iFrame.
    by iMod (ghost_map_elem_persist with "[$]") as "$".
  Qed.
  
End impl.
