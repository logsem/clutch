(** * Conventions shared by the executable environments

    An environment is written as a Rocq function of [obs : string → val].
    [obs t] is an ordinary closure [λ: <>, #()] supplied by the OCaml
    harness; the interpreter recognises the closures it handed out by
    physical identity and records a call [obs t v] as an observation
    [t: v] in the protocol trace.  Semantically an observation is a call of
    a function that ignores its argument, so it does not change the output
    distribution of the program. *)
From Stdlib Require Import String.
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup.

(** Leak ports [(leakSend, leakRecv)] that observe every call and permit
    every delivery: [leakRecv] answers [SOME ()].  This is the honest
    network for [F_AUTH], [F_OAUTH], [F_CHAN] and the key exchanges. *)
Definition deliver_ports (obs : string → val) (tag : string) : expr :=
  ((λ: "m", (obs (tag ++ ".send")%string) "m"),
   (λ: "from", (obs (tag ++ ".recv")%string) "from" ;; SOME #()%V))%E.

Section group_helpers.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (** Discrete logarithm by exhaustive search over the exponents [0..n]
      that the protocols sample; [-1] if there is none.  Only meant for the
      toy groups of the executable instances. *)
  Definition dlog : val :=
    λ: "x",
      (rec: "go" "e" :=
         if: #n < "e" then #(-1)
         else if: veq (g ^ "e") "x" then "e" else "go" ("e" + #1)) #0.

  (** An involutive masking of group elements, [mask k m = k · m⁻¹], for the
      one-message secure channel ([sec_channel_def], class [Mask]). *)
  Definition toy_mask : val := λ: "k" "m", "k" · ("m" ^-1).
End group_helpers.
