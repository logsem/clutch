From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth numbers gset_bij.
From clutch.prelude Require Import stdpp_ext.
From clutch.coneris Require Import coneris con_hash_interface2 con_hash_interface3.
Import Hierarchy.

Set Default Proof Using "Type*".

Section con_hash_impl3.
  
  Variable val_size:nat.
  Variable max_hash_size:nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.
  Context `{Hc: conerisGS Σ, 
              hash2: !con_hash2 val_size,
                 Htoken:inG Σ (authR natR)
    }.

  (** * Code *)

  Definition init_hash:=init_hash2.
  Definition compute_hash:=compute_hash2.
  Definition allocate_tape:=allocate_tape2.

  
  Definition hash_set_frag v γ_set γ_set' := (hash_set_frag2 v γ_set γ_set')%I.
  Definition hash_set n γ γ' γ_token:=
    (∃ ε,
        hash_set2 n γ γ' ∗
        own γ_token (● max_hash_size) ∗
        own γ_token (◯ n) ∗
        ⌜ (ε.(nonneg) = (((max_hash_size-1) * n)/2 - sum_n_m (λ x, INR x) 0%nat (n-1)) / (val_size + 1))%R⌝ ∗
      ↯ ε
    )%I.
  
  Definition hash_auth :=
    (hash_auth2 )%I.
  Definition hash_tape := hash_tape2.
  Definition hash_tape_auth  := hash_tape_auth2.

  Definition hash_frag := hash_frag2.

  Definition hash_token n γ := own γ (◯ n%nat).
  
  Definition con_hash_inv N f l hm (P:gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')} γ1 γ2 γ_tape γ4 γ5 γ_token γ_lock:=
    (con_hash_inv2 (N.@"1") f l hm P γ1 γ2 γ_tape γ4 γ5 γ_lock ∗
    inv (N.@"2") (∃ n, hash_set n γ2 γ5 γ_token))%I
  .

  (* Program Definition con_hash_impl3 : con_hash3 val_size max_hash_size max_hash_size_pos := *)
  (*   {| init_hash3:=init_hash; *)
  (*     allocate_tape3:=allocate_tape; *)
  (*     compute_hash3:=compute_hash; *)
      
  (*     con_hash_inv3 := con_hash_inv;   *)
  (*     hash_tape3:=hash_tape; *)
  (*     hash_frag3:=hash_frag; *)
  (*     hash_auth3:=hash_auth; *)
  (*     hash_tape_auth3 := hash_tape_auth; *)
  (*     hash_set3:=hash_set;  *)
  (*     hash_set_frag3:=hash_set_frag; *)
  (*     hash_token3 := hash_token; *)
  (*   |}. *)
  
        
  
  (* Program Definition con_hash_impl2 : con_hash2 val_size := *)
  (*   {| init_hash2:=init_hash; *)
  (*     allocate_tape2:=allocate_tape; *)
  (*     compute_hash2:=compute_hash; *)
      
  (*     con_hash_inv2 := con_hash_inv;  *)
  (*     hash_tape2:=hash_tape; *)
  (*     hash_frag2:=hash_frag; *)
  (*     hash_auth2:=hash_auth; *)
  (*     hash_tape_auth2 := hash_tape_auth; *)
  (*     hash_set2:=hash_set;  *)
  (*     hash_set_frag2:=hash_set_frag;  *)
  (*     con_hash_interface2.hash_tape_presample := hash_tape_presample;  *)
  (*     con_hash_presample2 := con_hash_presample;  *)
  (*     con_hash_init2 := con_hash_init;  *)
  (*     con_hash_alloc_tape2 := con_hash_alloc_tape;  *)
  (*     con_hash_spec2:=con_hash_spec *)
  (*   |} *)
  (* . *)
  (* Next Obligation. *)
  (*   iIntros (??????) "[??][??]". *)
  (*   iApply (hv_auth_exclusive with "[$][$]"). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (???????)"[??][??]". *)
  (*   iApply (hv_auth_frag_agree with "[$]"). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (????????) "[?[??]]". *)
  (*   iDestruct (hv_auth_duplicate_frag with "[$]") as "[? $]"; first done. *)
  (*   by iApply (con_hash_interface1.hash_auth_duplicate). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (?????) "[??]". *)
  (*   by iApply hv_auth_coll_free. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   rewrite /hash_frag. *)
  (*   iIntros (???????) "[??][??]". *)
  (*   iDestruct (hv_frag_frag_agree with "[$][$]") as "%". iPureIntro. naive_solver. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (????????) "[H1 H2][H3[H4 H5]]". *)
  (*   rewrite /hash_set_frag. *)
  (*   rewrite big_sepM_sep. *)
  (*   iDestruct "H5" as "[#H5 H6]". *)
  (*   rewrite /hash_auth. *)
  (*   iMod (con_hash_interface1.hash_auth_insert with "[$][$]") as "K"; first done. *)
  (*   iDestruct (con_hash_interface1.hash_auth_duplicate with "[$]") as "#?"; first apply lookup_insert. *)
  (*   iAssert (⌜v∉(map_to_list m).*2⌝)%I as "%H0". *)
  (*   { iIntros (H'). *)
  (*     apply elem_of_list_fmap_2 in H'. *)
  (*     destruct H' as ([??]&?&H1). simplify_eq. *)
  (*     rewrite elem_of_map_to_list in H1. *)
  (*     iDestruct (big_sepM_lookup with "[$]") as "H4"; first done. *)
  (*     simpl. *)
  (*     iCombine "H2 H4" gives "%H0". *)
  (*     cbv in H0. naive_solver. *)
  (*   }  *)
  (*   iMod (hv_auth_insert with "[$]") as "[$?]"; first done. *)
  (*   { rewrite Forall_forall. *)
  (*     intros x Hx. *)
  (*     intros ->. *)
  (*     by apply H0. } *)
  (*   rewrite big_sepM_insert; last done. *)
  (*   iFrame. *)
  (*   iDestruct (hash_frag_in_hash_set with "[$]") as "$". *)
  (*   rewrite /hash_set_frag. *)
  (*   iModIntro. rewrite big_sepM_sep. *)
  (*   by iFrame. *)
  (* Qed. *)
  
  (* Next Obligation. *)
  (*   iIntros (????) "?". *)
  (*   by iApply con_hash_interface1.hash_tape_valid. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (?????) "??". *)
  (*   iApply (con_hash_interface1.hash_tape_exclusive with "[$][$]"). *)
  (* Qed. *)

  
End con_hash_impl3.
