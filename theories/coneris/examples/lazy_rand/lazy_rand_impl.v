From iris.algebra Require Import gmap.
From clutch.coneris Require Import coneris abstract_tape hocap_rand_alt lock lazy_rand_interface.

Set Default Proof Using "Type*".


(* Section lemmas. *)
(*   Context `{!inG Σ (excl_authR (optionO (prodO natO natO)))}. *)

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
Section impl.
  Variable val_size:nat.
  Context `{Hc: conerisGS Σ,
              Hv: !ghost_mapG Σ () (option (nat*nat)),
                lo:lock, Hl: lockG Σ,
                    (* Hv: !inG Σ (excl_authR (optionO (prodO natO natO))), *)
                      Ht: !abstract_tapesGS Σ,
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
    (rand_tapes α (option_to_list n) γ.1 ∗ α ◯↪N ( val_size ; option_to_list n ) @ γ.2)%I.
  
  Definition rand_tape_auth m γ :=(([∗ set] α∈ dom m, rand_token α γ.1) ∗
                                   ● ((λ x, (val_size, option_to_list x))<$>m) @ γ.2)%I.
  

  Definition abstract_lazy_rand_inv N γ_tape:=
    (inv (N.@"tape") (∃ m, rand_tape_auth m γ_tape) ∗ is_rand (N.@"rand") γ_tape.1)%I.


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

  Definition rand_frag (res tid:nat) (γ:gname):=(() ↪[γ]□ Some (res, tid))%I.
  
  Definition option_duplicate (n:option (nat* nat)) γ:=
    match n with
    | Some (n1, n2) => rand_frag n1 n2 γ
    | None => (⌜True⌝)%I
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

  Lemma rand_tape_presample_impl N c P {HP:∀ n, Timeless (P n)} γ γ_view γ_lock E m α ε (ε2:fin (S val_size) -> R):
    ↑(N.@"rand")⊆E ->
    (∀ x, (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    lazy_rand_inv N c P γ γ_view γ_lock -∗
    rand_tape_auth m γ -∗ rand_tape_frag α None γ -∗ ↯ ε -∗
    state_update E E (∃ n, 
          ↯ (ε2 n) ∗
          rand_tape_auth (<[α:=Some (fin_to_nat n)]>m) γ ∗
          rand_tape_frag α (Some (fin_to_nat n)) γ).
  Proof. 
    iIntros (???) "(%&%&->&#[? Hinv]&#?) [Htokens Htauth] [Htape Hfrag] Herr".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%H'".
    rewrite lookup_fmap in H'. apply fmap_Some_1 in H'.
    destruct H' as (?&Hsome&?). simplify_eq.
    iMod (rand_tapes_presample with "[$][$][$]") as "(%&Htape&?)"; try done.
    iMod (abstract_tapes_presample with "[$][$]") as "[? H]".
    iFrame. iModIntro.
    iSplitL "Htokens".
    - by rewrite dom_insert_lookup_L.
    - by rewrite fmap_insert.
  Qed.

  Lemma lazy_rand_presample_impl N c P {HP: ∀ n, Timeless (P n)} γ γ_view γ_lock Q
    E  :
  ↑(N.@"tape") ⊆ E ->
  lazy_rand_inv N c P γ γ_view γ_lock -∗
  (∀ m,  rand_tape_auth m γ -∗
         state_update (E∖↑(N.@"tape")) (E∖↑(N.@"tape"))
           (∃ m', rand_tape_auth m' γ ∗ Q m m')
    ) -∗
    state_update E E (
        ∃ m m', Q m m'
      ).
  Proof.
    iIntros (?) "(%&%&->&#[Hinv ?]&#?) Hvs".
    iInv "Hinv" as ">(%&?)" "Hclose".
    iMod ("Hvs" with "[$]") as "(%&?&?)".
    iMod ("Hclose" with "[$]") as "_".
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
    iMod (ghost_map_alloc (<[():=None]> ∅)) as "(%&Hm&_)".
    wp_apply (newlock_spec (∃ res, P res ∗ rand_auth res _ ∗ _↦(option_to_val res))%I
                           with "[$HP $Hx $Hm //]"
             ).
    iIntros (??) "#Hlock".
    wp_pures.
    iMod (rand_inv_create_spec) as "(%&#Hrand)"; last first.
    - iMod (abstract_tapes_alloc ∅) as "(%&Hm&_)".
      iMod (inv_alloc _ _ (∃ m, rand_tape_auth m (_,_)) with "[Hm]") as "#Hinv".
      { iNext. iExists ∅. rewrite /rand_tape_auth. rewrite fmap_empty.
        iFrame. by rewrite dom_empty_L. }
      iApply "HΦ". iFrame "Hlock".
      rewrite /abstract_lazy_rand_inv. iExists (_,_).
      by iFrame "Hrand Hinv".
    - done.
  Qed.

  Lemma lazy_rand_alloc_tape_impl N c P {HP: ∀ n, Timeless (P n)} γ_tape γ_view γ_lock Q:
  {{{ lazy_rand_inv N c P γ_tape γ_view γ_lock ∗
      (∀ (m:gmap val (option nat)) α, ⌜α∉dom m⌝ -∗ |={⊤∖↑N.@"tape"}=> Q α)
  }}}
      allocate_tape_prog #()
      {{{ (α: val), RET α; rand_tape_frag α None γ_tape ∗ Q α }}}.
  Proof.
    iIntros (Φ) "[(%&%&->&#[Hinv ?]&_) Hvs] HΦ".
    rewrite /allocate_tape_prog.
    wp_pures.
    iApply pgl_wp_fupd.
    wp_apply (rand_allocate_tape_spec with "[//]") as (α) "[Htoken Hrand]"; first done.
    iInv "Hinv" as ">(%m&Htokens&Hauth)" "Hclose".
    iAssert (⌜α∉dom m⌝)%I as "%".
    { iIntros "%H".
      rewrite big_sepS_elem_of_acc; last done.
      iDestruct "Htokens" as "[? ?]".
      iApply (rand_token_exclusive with "[$][$]").
    }
    iMod ("Hvs" with "[//]") as "HQ".
    iMod (abstract_tapes_new with "[$]") as "[Hauth Htape]"; last first.
    - iMod ("Hclose" with "[Hauth Htoken Htokens]").
      + iExists (<[_:=_]> _). rewrite /rand_tape_auth.  rewrite fmap_insert. iFrame.
        rewrite dom_insert_L big_sepS_insert; last done.
        iFrame.
      + iApply "HΦ". by iFrame.
    - rewrite lookup_fmap. apply not_elem_of_dom_1 in H. by rewrite H.
  Qed.

  Lemma lazy_rand_spec_impl N c P {HP: ∀ n, Timeless (P n)} γ_tape γ_view γ_lock Q1 Q2 α (v:nat) (tid:nat):
  {{{ lazy_rand_inv N c P γ_tape γ_view γ_lock ∗
      ( ∀ n m, P n -∗ rand_auth n γ_view -∗ rand_tape_auth m γ_tape -∗ state_update (⊤∖↑N.@"tape") (⊤∖↑N.@"tape")
             match n with
             | Some (res, tid') => P n ∗ rand_auth n γ_view ∗ rand_tape_auth m γ_tape ∗ Q1 res tid'
             | None => ∃ n', rand_tape_frag α (Some n') γ_tape ∗ rand_tape_auth (<[α:=Some n']> m) γ_tape ∗
                              (rand_tape_frag α None γ_tape
                                      ={⊤∖↑N.@"tape"}=∗  P (Some (n', tid)) ∗ rand_auth (Some (n', tid)) γ_view ∗ Q2 n' tid)
             end                                        
      )
  }}}
      lazy_read_rand_prog c α #tid
      {{{ (res' tid':nat), RET (#res', #tid')%V;  (Q1 res' tid' ∨
                                                   Q2 res' tid'
                                )
      }}}.
  Proof.
    iIntros (Φ) "[(%&%&->&#[Hinv ?]&#Hlock) Hvs] HΦ".
    rewrite /lazy_read_rand_prog. wp_pures.
    wp_apply (acquire_spec with "[$]") as "[Hl (%res&HP&(Hauth & Hfrag & %Hvalid)&Hloc)]".
    wp_pures.
    wp_load.
    iApply state_update_pgl_wp.
    iInv ("Hinv") as ">(%&Htokens&Htauth)" "Hclose".
    iMod ("Hvs" with "[$][$Hauth $Hfrag//][$]") as "Hcont".
    destruct res as [[]|].
    - iDestruct "Hcont" as "(HP&Hauth &Htauth&HQ)".
      iMod ("Hclose" with "[$Htauth]") as "_".
      iModIntro. wp_pures.
      wp_apply (release_spec with "[$Hlock $Hl $HP $Hloc $Hauth]").
      iIntros. wp_pures.
      iApply "HΦ". by iFrame.
    - iDestruct "Hcont" as "(%&[Ht Htfrag] &[Htokens Htauth] & Hvs)".
      iMod ("Hclose" with "[$Htauth $Htokens]") as "_".
      iModIntro. wp_pures.
      wp_apply (rand_tape_spec_some with "[$]") as "Htape"; first done.
      iApply fupd_pgl_wp.
      iInv ("Hinv") as ">(%&Htokens&Htauth)" "Hclose".
      iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
      apply lookup_fmap_Some in Hsome.
      destruct Hsome as ([x|]&?&Hsome); simplify_eq.
      iMod (abstract_tapes_pop with "[$][$]") as "[Hauth Htape']".
      iMod ("Hvs" with "[$]") as "(HP&Hrand&HQ)".
      iMod ("Hclose" with "[Hauth Htokens]") as "_".
      { iExists (<[_:=None]>_).
        rewrite /rand_tape_auth. rewrite fmap_insert.
        rewrite dom_insert_lookup_L; last done. iFrame.
      }
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
      lazy_rand_interface.rand_tape_auth := rand_tape_auth;
      lazy_rand_interface.rand_auth := rand_auth;
      lazy_rand_interface.rand_frag := rand_frag;
      rand_inv:=lazy_rand_inv;
      rand_tape_presample:=rand_tape_presample_impl;
      lazy_rand_presample:=lazy_rand_presample_impl;
      lazy_rand_init:=lazy_rand_init_impl;
      lazy_rand_alloc_tape:=lazy_rand_alloc_tape_impl;
      lazy_rand_spec:=lazy_rand_spec_impl
    |}
  .
  Next Obligation.
    intros [[]|]?; rewrite /rand_auth/=; apply _.
  Qed.
  Next Obligation.
    rewrite /rand_tape_frag/=.
    iIntros (???) "[??]".
    iDestruct (rand_tapes_valid with "[$]") as "%H".
    by rewrite Forall_singleton in H.
  Qed.
  Next Obligation.
    rewrite /rand_tape_frag.
    iIntros (????) "[??][??]".
    iApply (rand_tapes_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    rewrite /rand_tape_auth/rand_tape_frag.
    iIntros (?? x ?) "[??][??]".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    apply lookup_fmap_Some in Hsome.
    by destruct Hsome as ([[]|]&?&Hsome); destruct x; simplify_eq.
  Qed.
  Next Obligation.
    rewrite /rand_auth.
    iIntros (???) "[??][??]".
    iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%?]".
    done.
  Qed.
  Next Obligation.
    rewrite /rand_auth/rand_frag.
    iIntros (????)"[H ?]H'".
    iCombine "H H'" gives "%H".
    destruct n; simpl in H; simplify_eq.
    rewrite /option_to_gmap in H. rewrite lookup_insert in H.
    by simplify_eq.
  Qed.
  Next Obligation.
    iIntros ([]?) "(?&#?&?)".
    iFrame. by iSplit.
  Qed.
  Next Obligation.
    rewrite /rand_frag.
    iIntros (?????) "H H'".
    iCombine "H H'" gives "%".
    iPureIntro. naive_solver.
  Qed.
  
End impl.
