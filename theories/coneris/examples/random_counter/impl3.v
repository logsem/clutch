From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap random_counter.

Set Default Proof Using "Type*".

Section filter.
  Definition filter_f (n:fin 4%nat):= bool_decide (fin_to_nat n<4)%nat.
  Definition filtered_list (l:list _) := filter filter_f l.
End filter.

Section impl3.

  Definition new_counter3 : val:= λ: "_", ref #0.
  Definition allocate_tape3 : val := λ: "_", AllocTape #4.
  Definition incr_counter_tape3 :val := rec: "f" "l" "α":=
                                          let: "n" := rand("α") #4 in
                                          if: "n" < #4
                                          then (FAA "l" "n", "n")
                                          else "f" "l" "α".
  Definition read_counter3 : val := λ: "l", !"l".
  Class counterG3 Σ := CounterG3 { counterG2_error::hocap_errorGS Σ;
                                   counterG2_tapes:: hocap_tapesGS Σ;
                                   counterG2_frac_authR:: inG Σ (frac_authR natR) }.

  Context `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ, !inG Σ (frac_authR natR)}.
End impl3. 
