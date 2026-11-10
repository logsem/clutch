(** * Environments for secure addition ([secure_add_def])

    The environment is the aggregator Charlie and the network: the client
    gets [(doInA, doInB)], the ports are [((sendAC, sendBC), chanLeak)]. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup dhke_def sec_channel_def secure_add_def.
From clutch_exec Require Import exec_common.

Section env_add.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (** Charlie's two messages, as received by the environment. *)
  Definition add_ports (obs : string → val) (mA mB : expr) : expr :=
    (((λ: "m", (obs "toC.A") "m" ;; mA <- SOME "m"),
      (λ: "m", (obs "toC.B") "m" ;; mB <- SOME "m")),
     deliver_ports obs "chan")%E.

  (** Honest run on uniformly chosen inputs: true iff the product of
      Charlie's two messages is the product of the inputs. *)
  Definition env_add_honest (obs : string → val) : val :=
    λ: "X",
      let: "x" := rand #n in
      let: "y" := rand #n in
      let: "mA" := ref NONE in
      let: "mB" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("inA", "inB") := "ops" in "inA" "x" ;; "inB" "y")
          (add_ports obs "mA" "mB") ;;
      match: !"mA" with
        NONE => #false
      | SOME "a" =>
          match: !"mB" with
            NONE => #false
          | SOME "b" =>
              (obs "aggregate") ("a" · "b") ;;
              match: vg_of_int "x" with
                NONE => #false
              | SOME "gx" =>
                  match: vg_of_int "y" with
                    NONE => #false
                  | SOME "gy" => veq ("a" · "b") ("gx" · "gy")
                  end
              end
          end
      end.

  (** True iff Alice's message to Charlie is her input, i.e. her mask is
      the unit.  The mask is uniform in both worlds. *)
  Definition env_add_peek (obs : string → val) : val :=
    λ: "X",
      let: "x" := rand #n in
      let: "mA" := ref NONE in
      let: "mB" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("inA", "inB") := "ops" in "inA" "x" ;; "inB" #0)
          (add_ports obs "mA" "mB") ;;
      match: !"mA" with
        NONE => #false
      | SOME "a" => match: vg_of_int "x" with NONE => #false | SOME "gx" => veq "a" "gx" end
      end.
End env_add.
