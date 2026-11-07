(* Realising the authenticated channel [F_AUTH] over the raw network with a
   preshared key.

   The protocol [AUTH] runs both parties.  Its ports [effs = (doSend, doRecv)]
   are the raw network, i.e. the environment: every message it sends is seen
   by the environment, and what it receives is whatever the environment
   injects.  Each direction has its own preshared one-time MAC key
   [(k1, k2)], sampled at setup, with [tag m = m^k1 · g^k2].  A direction
   verifies the first pair it is given and remembers the verdict.

   The simulator [S_AUTH] turns [F_AUTH]'s leak-and-permit interface into the
   raw network's: it tags the leaked message with its own key, records the
   pair, and permits delivery iff the environment injects exactly that pair.

   Slots follow [F_AUTH]: messages with destination [InjL] live in slot 1 and
   are read by a receiver [InjR], and symmetrically. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import metatheory class_instances.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

Section auth_def.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  (* [tag k1 k2 m = m^k1 · g^k2] *)
  Definition tag : val := λ: "k1" "k2" "m", "m" ^ "k1" · g ^ "k2".

  Definition AUTH : val := λ: <>,
    let: "k1a" := sample #()%V in let: "k2a" := sample #()%V in
    let: "k1b" := sample #()%V in let: "k2b" := sample #()%V in
    let: "sent1" := ref #false in let: "sent2" := ref #false in
    let: "dec1" := ref #false in let: "dec2" := ref #false in
    let: "res1" := ref NONEV in let: "res2" := ref NONEV in
    λ: "f" "effs",
      let, ("doSend", "doRecv") := "effs" in
      effect "send"
        effect "recv"
        let: "doASend" := (λ: "m", do: "send" "m") in
        let: "doARecv" := (λ: "p", do: "recv" "p") in
        handle: handle: "f" ("doASend", "doARecv") with
      | effect "send" "payload", rec "k" =>
          let, ("m", "dst") := "payload" in
          match: "dst" with
            InjL <> =>
              (if: !"sent1" then #()%V
               else "sent1" <- #true;; "doSend" (("m", tag "k1a" "k2a" "m"), "dst"));;
              "k" #()%V
          | InjR <> =>
              (if: !"sent2" then #()%V
               else "sent2" <- #true;; "doSend" (("m", tag "k1b" "k2b" "m"), "dst"));;
              "k" #()%V
          end
      | return "y" => #()%V end with
      | effect "recv" "from", rec "k" =>
          (* a receiver [InjL] reads slot 2 (key b); a receiver [InjR] reads slot 1 (key a) *)
          let: "k1" := match: "from" with InjL <> => "k1b" | InjR <> => "k1a" end in
          let: "k2" := match: "from" with InjL <> => "k2b" | InjR <> => "k2a" end in
          let: "dec" := match: "from" with InjL <> => "dec2" | InjR <> => "dec1" end in
          let: "res" := match: "from" with InjL <> => "res2" | InjR <> => "res1" end in
          if: !"dec" then "k" !"res"
          else
            match: "doRecv" "from" with
              NONE => "k" NONEV
            | SOME "p" =>
                let, ("m'", "t'") := "p" in
                let: "r" := if: veq "t'" (tag "k1" "k2" "m'") then SOME "m'" else NONEV in
                "dec" <- #true;; "res" <- "r";; "k" "r"
            end
      | return "y" => #()%V end.

  Definition S_AUTH : val := λ: <>,
    let: "k1a" := sample #()%V in let: "k2a" := sample #()%V in
    let: "k1b" := sample #()%V in let: "k2b" := sample #()%V in
    let: "tagged1" := ref #false in let: "tagged2" := ref #false in
    let: "tag1" := ref (g, g) in let: "tag2" := ref (g, g) in
    let: "dec1" := ref #false in let: "dec2" := ref #false in
    let: "acc1" := ref #false in let: "acc2" := ref #false in
    λ: "f" "effs",
      let, ("doSend", "doRecv") := "effs" in
      "f" ((λ: "payload",
              let, ("m", "dst") := "payload" in
              match: "dst" with
                InjL <> => let: "t" := tag "k1a" "k2a" "m" in
                           "tagged1" <- #true;; "tag1" <- ("m", "t");; "doSend" (("m", "t"), "dst")
              | InjR <> => let: "t" := tag "k1b" "k2b" "m" in
                           "tagged2" <- #true;; "tag2" <- ("m", "t");; "doSend" (("m", "t"), "dst")
              end),
           (λ: "from",
              let: "tagged" := match: "from" with InjL <> => "tagged2" | InjR <> => "tagged1" end in
              let: "tg" := match: "from" with InjL <> => "tag2" | InjR <> => "tag1" end in
              let: "dec" := match: "from" with InjL <> => "dec2" | InjR <> => "dec1" end in
              let: "acc" := match: "from" with InjL <> => "acc2" | InjR <> => "acc1" end in
              if: !"dec" then (if: !"acc" then SOME #(0%nat) else NONEV)
              else
                match: "doRecv" "from" with
                  NONE => NONEV
                | SOME "p" =>
                    let, ("m'", "t'") := "p" in
                    let, ("m", "t") := !"tg" in
                    let: "ok" := !"tagged" && veq "m'" "m" && veq "t'" "t" in
                    "dec" <- #true;; "acc" <- "ok";;
                    (if: "ok" then SOME #(0%nat) else NONEV)
                end)).

  (* The protocol and the simulator are factories: they allocate their keys
     and state when called.  [AsRecV] lets the pure-step tactics call them
     without unfolding. *)
  #[global] Instance AUTH_as_recv : AsRecV AUTH BAnon BAnon _ := eq_refl.
  #[global] Instance S_AUTH_as_recv : AsRecV S_AUTH BAnon BAnon _ := eq_refl.

End auth_def.
