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
                                                    let: "x'" := SOME (rand_tape "α", "tid") in 
                                                    "x" <- "x'";;
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
  
  Definition rand_auth (n:option (nat*nat)) γ :=
    (ghost_map_auth γ 1 (option_to_gmap n) ∗
     ⌜option_valid n⌝)%I.

  Definition rand_frag (res tid:nat) (γ:gname):=(() ↪[γ]□ Some (res, tid))%I.
  
  Definition lazy_rand_inv N c P{HP: ∀ n, Timeless (P n)}  γ_tape γ_view γ_lock :=
    (∃ lk (l:loc),
      ⌜c=(lk, #l)%V⌝ ∗
      abstract_lazy_rand_inv N γ_tape ∗
      is_lock (L:=Hl) γ_lock lk (∃ res, P res ∗ rand_auth res γ_view ∗ l↦(option_to_val res)))%I.
  
  (* Program Definition lazy_rand_impl : lazy_rand val_size := *)
  (*   {| init_lazy_rand := init_lazy_rand_prog; *)
  (*     allocate_tape := allocate_tape_prog; *)
  (*     lazy_read_rand := lazy_read_rand_prog; *)
  (*     lazy_rand_interface.rand_tape_frag := rand_tape_frag; *)
  (*     lazy_rand_interface.rand_tape_auth := rand_tape_auth; *)
  (*     lazy_rand_interface.rand_auth := rand_auth; *)
  (*     lazy_rand_interface.rand_frag := rand_frag; *)
  (*     rand_inv:=lazy_rand_inv; *)
  (*   |} *)
  (* . *)
End impl.
