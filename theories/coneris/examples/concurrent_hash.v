From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn spin_lock hash atomic lock.

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
      "h" (rand #val_size);;
      release "lock"
  .

  Definition multiple_parallel : val :=
    rec: "multiple_parallel" "num" "f" :=
      if: "num" ≤ #0 then #() else
       "f" #() ||| "multiple_parallel" ("num"-#1) "f"
  .

  Definition concurrent_hash_prog : expr :=
    let: "h" := init_hash val_size #() in
    let: "lock" := newlock #() in
    multiple_parallel #insert_num (hash_once_prog "h" "lock");;
    "h".

  Context `{!conerisGS Σ, !spawnG Σ, !lockG Σ}.

  Lemma hash_once_prog_spec γ l f:
    {{{ is_lock γ l (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m) ∗ ↯ err }}}
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
    wp_apply (wp_insert_amortized with "[$]").
    - admit.
    - iIntros (?) "(%&?&%)". wp_pures.
      wp_apply (release_spec with "[-HΦ]").
      + iFrame. iSplitR; first iApply "H". iFrame.
      + done.
  Admitted.

  Lemma hash_once_prog_spec' γ (l:val) (f:val) E:
    ⊢ <<{ is_lock γ l (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m) ∗ ↯ err }>>
      hash_once_prog f l #() @ E
      <<{ ∃∃ (v:val), True | RET v }>>.
  Proof.
  Admitted. 
        
  
  Lemma concurrent_hash_spec :
    {{{ ↯ (INR insert_num * err)%R }}}
      concurrent_hash_prog
      {{{ (f:val), RET f; ∃ m, inv nroot (coll_free_hashfun_amortized val_size max_hash_size f m)}}}.
  Proof.
    rewrite /concurrent_hash_prog.
    iIntros (Φ) "Herr HΦ".
    wp_apply wp_init_hash as (h) ">Hf"; first done.
    wp_pures.
    
  Admitted.
  
End concurrent_hash.
