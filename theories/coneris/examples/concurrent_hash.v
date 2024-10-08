From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn spin_lock hash atomic lock.
From clutch.coneris.lib Require Import list.

Set Default Proof Using "Type*".

Section concurrent_hash.
  Variable val_size : nat.
  Variable insert_num : nat.
  Variable max_hash_size : nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.

  Definition err := amortized_error val_size max_hash_size max_hash_size_pos.

  Context {Hineq : (insert_num <= max_hash_size)%nat}.

  Local Existing Instance spin_lock.
  
  Definition hash_once_prog : val :=
    λ: "h" "lock" "_",
      acquire "lock";;
      let: "input" := (rand #val_size) in
      let: "output" := "h" "input" in
      release "lock";;
      ("input", "output")
  .

  Definition multiple_parallel : val :=
    rec: "multiple_parallel" "num" "f" :=
      if: "num" ≤ #0 then list_nil else
        let, ("hd", "tl") :=  ("f" #() ||| "multiple_parallel" ("num"-#1) "f") in
        list_cons "hd" "tl"
  .

  Definition concurrent_hash_prog : expr :=
    let: "h" := init_hash val_size #() in
    let: "lock" := newlock #() in
    ("h", multiple_parallel #insert_num (hash_once_prog "h" "lock")).

  Context `{!conerisGS Σ, !spawnG Σ, !lockG Σ, inG Σ (authR natR)}. 

  Lemma hash_once_prog_spec γlock γ l f:
    {{{ is_lock γlock l (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ) ∗ ↯ err ∗ own γ (◯ 1%nat) }}}
      hash_once_prog f l #()
      {{{ (v:val), RET v; True }}}.
  Proof.
    iIntros (Φ) "[#H Herr] HΦ".
    rewrite /hash_once_prog.
    wp_pures.
    wp_apply (acquire_spec with "H") as "[Hl [% K]]".
    wp_pures.
    wp_apply wp_rand; first done.
    iIntros.
    wp_pures.
    wp_apply (wp_insert_amortized with "[$]").
    iIntros (?) "(%&?&%)". wp_pures.
    wp_apply (release_spec with "[-HΦ]").
    - iFrame. iSplitR; first iApply "H". iFrame.
  Admitted.
  (*   - done. *)
  (* Qed. *)
  
  Lemma concurrent_hash_spec :
    {{{ ↯ (INR insert_num * err)%R }}}
      concurrent_hash_prog
      {{{ (f:val), RET f; ∃ γ γlock l,  is_lock γlock l (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ)}}}.
  Proof.
    rewrite /concurrent_hash_prog.
    iIntros (Φ) "Herr HΦ".
    wp_apply wp_init_hash as (h) ">Hf"; first done.
    wp_pures.
    
  Admitted.
  
End concurrent_hash.
