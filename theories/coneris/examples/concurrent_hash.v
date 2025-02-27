From iris.base_logic.lib Require Import invariants.
From coneris.coneris Require Import coneris par spawn spin_lock hash atomic lock.
From coneris.coneris.lib Require Import list.

Set Default Proof Using "Type*".

(** This example uses the spec from hash.v to derive a concurrent hash with a simple lock 
    To see a more modular (and structured) example of the hash, see the files in /examples/hash/
*)

Section concurrent_hash.
  Variable val_size : nat.
  Variable insert_num : nat.
  Variable max_hash_size : nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.

  Definition err := amortized_error val_size max_hash_size max_hash_size_pos.
  Local Opaque amortized_error.


  Local Existing Instance spin_lock.
  
  Definition hash_once_prog : val :=
    λ: "h" "lock" "_",
      acquire "lock";;
      let: "input" := (rand #val_size) in
      let: "output" := "h" "input" in
      release "lock";;
      ("input", "output")
  .
  
  Definition hash_once_prog_specialized (h lock:val) : val :=
    λ: "_",
      acquire lock;;
      let: "input" := (rand #val_size) in
      let: "output" := h "input" in
      release lock;;
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

  Context `{!conerisGS Σ, !spawnG Σ, !lockG Σ, !amortized_hashG Σ}. 

  Lemma hash_once_prog_spec γlock γ1 γ2 l f:
    {{{ is_lock γlock l (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2) ∗ ↯ err ∗ own γ1 (◯ 1%nat) }}}
      (hash_once_prog_specialized f l) #()
      {{{ (k v:nat), RET (#k, #v)%V; hash_view_frag k v γ2 }}}.
  Proof.
    clear.
    iIntros (Φ) "[#H Herr] HΦ".
    rewrite /hash_once_prog_specialized.
    wp_pures.
    wp_apply (acquire_spec with "H") as "[Hl [% K]]".
    wp_pures.
    wp_apply wp_rand; first done.
    iIntros.
    wp_pures.
    wp_apply (wp_insert_amortized with "[$]").
    iIntros (v) "(%m' & H' & % & % & % & Hfrag)".
    wp_pures.
    wp_apply (release_spec with "[-HΦ Hfrag]") as "_"; first (iFrame "H"; iFrame).
    wp_pures.
    by iApply "HΦ".
  Qed.

  
  Context {Hineq : (insert_num <= max_hash_size)%nat}.

  Lemma multiple_parallel_spec Ps (num:nat) (f:val) Q:
    length Ps = num ->
    {{{ ([∗ list] k↦P ∈ Ps,
           {{{ P }}}
             f #()
             {{{ v, RET v; Q v }}}) ∗
        [∗ list] k↦P∈Ps, P
    }}}
      multiple_parallel #num f
      {{{ v, RET v;
          ∃ returnl,
            ⌜length returnl = num⌝ ∗
            ⌜is_list returnl v⌝ ∗
            [∗ list] k↦x∈ returnl, Q x
      }}}.
  Proof.
    clear -spawnG0.
    iIntros (Hlen Φ) "[H1 H2] HΦ".
    iLöb as "IH" forall (Ps num Hlen Φ) "H1 H2 HΦ".
    rewrite /multiple_parallel.
    wp_pures.
    case_bool_decide as K.
    { wp_pures.
      iApply "HΦ".
      iExists [].
      simpl. iPureIntro. repeat split; lia.
    }
    wp_pures.
    destruct num as [|num]; first lia.
    wp_pures.
    rewrite -/multiple_parallel.
    destruct Ps as [|P Ps]; first done.
    iDestruct "H1" as "[H1 H1']".
    iDestruct "H2" as "[H2 H2']".
    wp_apply (wp_par (λ x, Q x) with "[H1 H2][H1' H2']").
    { wp_apply ("H1" with "[$]"). by iIntros. }
    { wp_pures.
      replace (_-_)%Z with (Z.of_nat num) by lia.
      simpl in Hlen. 
      iApply ("IH" with "[][$H1'][$H2']"); first (iPureIntro; by simplify_eq).
      iNext.
      iIntros (v) "H".
      iExact "H".
    }
    simpl.
    iIntros (v1 v2) "[H1 (%&%&%&H2)]".
    iNext. wp_pures.
    wp_apply (wp_list_cons with "[//]").
    iIntros (v) "%".
    iApply "HΦ".
    iExists (_::_).
    iFrame.
    simpl.
    iPureIntro; split; [congruence|done].
  Qed.

  
  Lemma concurrent_hash_spec :
    {{{ ↯ (INR insert_num * err)%R }}}
      concurrent_hash_prog
      {{{ (f lv:val), RET (f, lv)%I;
          ∃ γ1 γ2 γlock l (ls : list val),
            is_lock γlock l (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2)∗
                                  ⌜is_list ls lv⌝ ∗
                                  ⌜length ls = insert_num⌝ ∗
                                  ([∗ list] k ↦ x ∈ ls, ∃ (k v:nat), ⌜x=(#k, #v)%V⌝ ∗ hash_view_frag k v γ2) ∗
                                  own γ1 (◯ (max_hash_size - insert_num)%nat)
      }}}.
  Proof.
    rewrite /concurrent_hash_prog.
    iIntros (Φ) "Herr HΦ".
    wp_apply (wp_init_hash_amortized _ max_hash_size) as (f) ">(%γ1 & %γ2 & Hf & Htoken)"; [done..|].
    wp_pures.
    wp_apply ((newlock_spec (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2)%I) with "[$Hf]").
    iIntros (lk γlock) "#Hlock".
    wp_pures.
    replace max_hash_size with (insert_num + (max_hash_size-insert_num))%nat at 1 by lia.
    iDestruct "Htoken" as "[Htoken Htoken']".
    iAssert ([∗ list] k↦P∈repeat (↯ err ∗ own γ1 (◯ 1%nat)) insert_num, P)%I with "[Htoken Herr]" as "HPs".
    { clear.
      iInduction insert_num as [|insert_num'] "IH" forall "Htoken Herr"; first done.
      replace (S insert_num') with (1+insert_num')%nat by lia.
      iDestruct "Htoken" as "[Htoken Htoken']".
      rewrite plus_INR Rmult_plus_distr_r.
      iDestruct (ec_split with "[$]") as "[Herr Herr']".
      - replace (INR _) with 1%R by (simpl; lra).
        rewrite Rmult_1_l. by simpl.
      - apply Rmult_le_pos; last by simpl.
        apply pos_INR.
      - simpl. 
        rewrite Rmult_1_l. iFrame.
        iApply ("IH" with "[$][$]").
    }
    rewrite /hash_once_prog.
    wp_pures.
    rewrite -/(hash_once_prog_specialized f lk).
    wp_apply (multiple_parallel_spec _ _ _
                (λ (x:val), ∃ (k v:nat), ⌜x=(#k,#v)%V⌝ ∗ hash_view_frag k v γ2)%I with "[$HPs]"); first by rewrite repeat_length.
    - iInduction insert_num as [|?] "IH" forall (Hineq); first done.
      simpl.
      iSplit; last (iApply "IH"; iPureIntro; lia).
      iIntros (Φ') "!>[H1 H2]HΦ".
      iApply (hash_once_prog_spec with "[$H1 $H2//]").
      iIntros.
      iNext. iIntros (??) "H'". iApply "HΦ".
      iExists k, v.
      by iFrame "H'".
    - iIntros (?) "(%&%&%&?)".
      wp_pures.
      iApply "HΦ".
      iModIntro. iExists _, _, _, _, _.
      iSplit; first done.
      by iFrame.
  Qed.
      
  
End concurrent_hash.
