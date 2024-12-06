From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris hash_view_interface seq_hash_interface lock.

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


Section con_hash_impl.

  Context `{Hcon:conerisGS Σ, sh:@seq_hash Σ Hcon h hvG0 val_size, shG:seq_hashG Σ, l:lock, lockG Σ}.
  Context `{inG Σ (excl_authR (gmapO nat natO)), inG Σ (excl_authR natO)}.
  
  Definition init_con_hash := init_hash.
  Definition allocate_tape:= seq_hash_interface.allocate_tape.

  Definition compute_con_hash (h l:val):val:=
    λ: "_",
      acquire l;;
      let: "output" := compute_hash "input" in
      release l;;
      "output".

  Definition abstract_con_hash (f:val) (γ1:seq_hash_tape_gname) (γ2:hv_name) γ3 γ4 : iProp Σ :=
    ∃ m tape_m,
      abstract_seq_hash (L:=shG) f m tape_m γ1 γ2 ∗
      own γ3 (●E m) ∗
      own γ4 (●E (length (map_to_list m) + length (tape_m_elements tape_m)))
  .

  Definition concrete_con_hash (f:val) (m:gmap nat nat) γ : iProp Σ:=
    concrete_seq_hash (L:=shG) f m ∗
    own γ (◯E m).

End con_hash_impl.

