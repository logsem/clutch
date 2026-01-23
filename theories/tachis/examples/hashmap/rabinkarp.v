(** * Rabin Karp string detection *)
From clutch.tachis Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Stdlib Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
From Stdlib Require Import Lra.
From clutch.tachis.examples.hashmap Require Export hash.
From clutch.tachis.examples.lib Require Export list.


Set Default Proof Using "Type*".

Section rabin_karp.

  Context`{!tachisGS Σ CostTick}.

  Variable string_to_nat: val.
  Variable string_to_nat_specialized: val->nat.
  Axiom wp_string_to_nat:
    ∀ (v:val) E,
    {{{ True }}}
      string_to_nat v @ E
      {{{ (n:nat), RET #n; ⌜n=string_to_nat_specialized v⌝}}}.
  Hypothesis (string_to_nat_inj: Inj (=) (=) string_to_nat_specialized).

  Definition rk_helper : val :=
    (rec: "helper" "s" "p" "hf" "lp" "hp" "idx":=
       if: "idx" < list_length "s" - "lp" + #1
       then
         let: "w":= list_inf "idx" ("idx"+"lp") "s" in
         let: "h":= "hf" (string_to_nat "w") in
         tick #1 ;;
         if: "h" = "hp"
         then if: (tick "lp";; "w" = "p")
              then SOME "idx"
              else "helper" "s" "p" "hf" "lp" "hp" ("idx" + #1)
         else "helper" "s" "p" "hf" "lp" "hp" ("idx" + #1)
       else NONE
    ).

  Definition rk : val :=
    λ: "s" "p" "hf",
      let: "lp" := list_length "p" in
      tick #1;;
      let: "hp" := "hf" (string_to_nat "p") in
      match: rk_helper "s" "p" "hf" "lp" "hp" #0
      with
      | SOME "x" => "x"
      | NONE => #(-1)
      end
  .

  Variables p s:list nat.
  Definition p_len := length p.
  Definition s_len:= length s.
  Hypothesis (Hineq:p_len <= s_len).
  Definition val_size := s_len * s_len.

  Lemma wp_rk pv sv f E:
    is_list p pv -> is_list s sv -> 
    {{{ ⧖ (1+2*s_len) ∗ hashfun val_size f ∅ }}}
      rk sv pv f@E
      {{{ (z:Z), RET #z; ∃ m, hashfun val_size f m ∗ if bool_decide (z=-1)%Z then True else ⌜p=take p_len (drop (Z.to_nat z) s)⌝}}}.
  Proof.
    iIntros (Hp Hs Φ) "[Hx Hhf] HΦ".
    rewrite /rk.
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (?) "->".
    replace (length _) with p_len; last done.
    wp_pures.
    wp_pure.
    { pose proof pos_INR s_len. lra. } wp_pures.
    replace (_+_-_)%R with (2*s_len)%R; last lra.
    wp_apply wp_string_to_nat; first done.
    iIntros (?) "->".
    wp_apply (wp_insert with "[$Hhf]").
    { set_solver. }
    iIntros (hp) "Hhf".
    wp_pures.
  Abort. 
      
  
End rabin_karp.
