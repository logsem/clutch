From clutch.eris Require Export eris.


Section warmup.
  Context `{!erisGS Σ}.

  (*

     Eris is a higher-order separation logic to reason about
     probabilistic programs. The core concept of Eris is
     "error credits", a novel separation logic resource.
     Ownership of ε ∈ [0,1] error credits is denoted ↯ ε.
     When specifying a program e through a triple

     {{{ ↯ ε }}} e @ E {{{ v, RET v; φ v }}}

     the intended meaning of the specification is that the
     probability of e terminating in a value v that does not
     satisfy φ v, is at most ε.

     Let's begin with a simple example

  *)

  Definition φ v :iProp Σ:= (⌜v = #true⌝)%I.

  Definition coin_flip_prog : expr :=
    if: rand #2 <= #0 then #false else #true.

  (*

     Here, rand #2 samples uniformly from the set {0,1,2}.
     The program therefore returns #false with probability
     1/3, and #true with probability 2/3. Let's write a
     specification that captures this idea.

  *)


  Lemma coin_flip_spec E :
    {{{ ↯ (/3) }}} coin_flip_prog @ E {{{ v, RET v; φ v}}}.
  Proof.
    (* In Eris, as in Iris, triples are defined in terms
       of a primitive WP notion.
    *)
    iIntros (Ψ) "Herr HΨ".
    rewrite /coin_flip_prog.
    wp_apply (wp_rand_err_int _ _ 0 with "[-]").
    iSplitL "Herr".
    - simpl.
      assert (1 + 1 + 1 = 3)%R as -> by lra.
      iFrame.
    - iIntros (x) "[[%Hx1  %Hx2] %Hx3]".
      wp_pures.
      rewrite bool_decide_eq_false_2; last by lia.
      wp_pures.
      iApply "HΨ".
      done.
  Qed.


End warmup.
