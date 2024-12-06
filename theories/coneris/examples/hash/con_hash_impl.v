From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris hocap_rand lib.map abstract_tape hash_view_interface lock.

Set Default Proof Using "Type*".
(* Concurrent hash impl*)
Section lemmas.
  Context `{!inG Σ (excl_authR natO)}.

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

Section lemmas'.
  Context `{!inG Σ (excl_authR (gmapO nat natO))}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc' b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree' γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update' γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

End lemmas'.


Class con_hashG (Σ:gFunctors) := ConhashG {
                                     conhashG_tapesG::inG Σ (excl_authR (gmapO nat natO));
                                     conhashG_sizeG::inG Σ (excl_authR natO);
                                     conhashG_conerisG::conerisGS Σ;
                                     conhashG_rand::@rand_spec Σ conhashG_conerisG;
                                     conhashG_randG:randG Σ;
                                     conhashG_hv::@hash_view Σ conhashG_conerisG;
                                     conhashG_hvG: hvG Σ;
                                     conhashG_abstract_tapesG::abstract_tapesGS Σ;
                                     conhashG_lock::lock;
                                     conhashG_lockG:lockG Σ
                                     
}.
Section con_hash_impl.
  Context `{con_hashG Σ}.
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

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      let: "l" := newlock #() in
      ("l", compute_hash "hm").

  Definition allocate_tape : val :=
    λ: "_",
      rand_allocate_tape #val_size.

  Definition compute_con_hash :val:=
    λ: "lhm" "v" "α",
      let, ("l", "hm") := "lhm" in
      acquire "l";;
      let: "output" := compute_hash "hm" "v" "α" in
      release "l";;
      "output".

  Definition compute_con_hash_specialized (lhm:val):val:=
    λ: "v" "α",
      let, ("l", "hm") := lhm in
      acquire "l";;
      let: "output" := (compute_hash "hm") "v" "α" in
      release "l";;
      "output".

  Definition tape_m_elements (tape_m : gmap val (list nat)) :=
    concat (map_to_list tape_m).*2.
  
  Definition abstract_con_hash (f:val) (l:val) (hm:loc) γ1 γ2 γ3 γ4 : iProp Σ :=
    ∃ m tape_m ,
      ⌜f=compute_con_hash_specialized (l, #hm)%V⌝ ∗
      ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝ ∗
      (* the tapes*)
      ● ((λ x, (val_size, x))<$>tape_m) @ γ1 ∗
      ([∗ map] α ↦ t ∈ tape_m,  rand_tapes (L:=conhashG_randG) α (val_size, t)) ∗
      hv_auth (L:=conhashG_hvG) m γ2 ∗
      ⌜NoDup (tape_m_elements tape_m ++ (map_to_list m).*2)⌝ ∗
      own γ3 (●E m) ∗
      own γ4 (●E (length (map_to_list m) + length (tape_m_elements tape_m)))
  .

  Definition concrete_con_hash (hm:loc) (m:gmap nat nat) γ : iProp Σ:=
    map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
    own γ (◯E m).

End con_hash_impl.

