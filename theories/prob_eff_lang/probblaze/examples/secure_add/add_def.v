From clutch.prob_eff_lang.probblaze Require Export notation valgroup p_composition.
From clutch.prob_eff_lang.probblaze.examples Require Export def_dhke sec_channel_def.
From clutch.prob_eff_lang.probblaze Require Import logic sem_types sem_def sem_row.

Import fingroup.

Import valgroup_notation.

(** Two-party secure addition with an untrusted aggregator.

    Alice holds [x], Bob holds [y]; the aggregator -- played by the
    environment, which is also the network -- should learn [x · y] and
    nothing else.

    1. Alice samples a mask [r], sends [r] to Bob over the secure channel
       [F_CHAN] and sends [x · r] to the aggregator.
    2. Bob, once he has received [r], sends [y · r^-1] to the aggregator.
    3. The aggregator computes [(x · r) · (y · r^-1) = x · y]. *)

Section secure_add.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* Real protocol. [toC] are the operations of the aggregator (the env);
     [chan] are [doSecSend] and [doSecRecv] of the Alice-to-Bob [F_CHAN]. *)
  Definition π_ADD : val :=
    λ: "f" "effs",
      let, ("toC", "chan") := "effs" in
      let, ("sendAC", "sendBC") := "toC" in
      let, ("sAB", "rAB") := "chan" in
      let: "doneA" := ref #false in
      let: "doneB" := ref #false in
      effect "add"
        let: "doInA" := (λ: "x", do: "add" (InjL "x")) in
        let: "doInB" := (λ: "y", do: "add" (InjR "y")) in
        handle: "f" ("doInA", "doInB") with
    | effect "add" "p", rec "k" =>
        match: "p" with
        (* Alice *)
        | InjL "x" =>
            match: vg_of_int "x" with
            | NONE => "k" #()%V
            | SOME "x" =>
                if: !"doneA" then "k" #()%V else
                  ("doneA" <- #true;;
                   let: "r" := g^(sample #()%V) in
                   "sAB" (int_of_vg "r");;
                   "sendAC" ("x" · "r");;
                   "k" #()%V)
            end
        (* Bob *)
        | InjR "y" =>
            match: vg_of_int "y" with
            | NONE => "k" #()%V
            | SOME "y" =>
                if: !"doneB" then "k" #()%V else
                  match: "rAB" #()%V with
                  | NONE => "k" #()%V
                  | SOME "r" =>
                      "doneB" <- #true;;
                      "sendBC" ("y" · ("r"^-1));;
                      "k" #()%V
                  end
            end
        end
    | return "y" => "y" end.

  (* Ideal functionality. The adversary learns that Alice gave her input,
     decides whether Bob's input is accepted (mirroring the delivery of [r]
     in the real world), and receives the output [x · y]. *)
  Definition F_ADD : val :=
    λ: "f" "leaks",
      let, ("leakA", "leakB", "leakOut") := "leaks" in
      let: "lx" := ref NONEV in
      let: "ly" := ref NONEV in
      effect "add"
        let: "doInA" := (λ: "x", do: "add" (InjL "x")) in
        let: "doInB" := (λ: "y", do: "add" (InjR "y")) in
        handle: "f" ("doInA", "doInB") with
    | effect "add" "p", rec "k" =>
        match: "p" with
        (* Alice *)
        | InjL "x" =>
            match: vg_of_int "x" with
            | NONE => "k" #()%V
            | SOME "x" =>
                match: !"lx" with
                | NONE => "lx" <- SOME "x";; "leakA" #()%V;; "k" #()%V
                | SOME <> => "k" #()%V
                end
            end
        (* Bob *)
        | InjR "y" =>
            match: vg_of_int "y" with
            | NONE => "k" #()%V
            | SOME "y" =>
                match: !"ly" with
                | SOME <> => "k" #()%V
                | NONE =>
                    match: "leakB" #()%V with
                    | NONE => "k" #()%V
                    | SOME <> =>
                        match: !"lx" with
                        | NONE => "k" #()%V
                        | SOME "x" =>
                            "ly" <- SOME "y";;
                            "leakOut" ("x" · "y");;
                            "k" #()%V
                        end
                    end
                end
            end
        end
    | return "y" => "y" end.

  (* Simulator. It handles the leaks of [F_ADD] and reproduces what the
     real world shows the env: the leaks of [F_CHAN] (raised with the same
     [alice]/[bob] tags as [F_CHAN]) and the two messages to the
     aggregator. *)
  Definition S_ADD : val :=
    λ: "f" "effs",
      let, ("toC", "chanLeak") := "effs" in
      let, ("sendAC", "sendBC") := "toC" in
      let, ("lsAB", "lrAB") := "chanLeak" in
      let: "lu" := ref NONEV in
      effect "leak"
        let: "leakA" := (λ: <>, do: "leak" (InjL #()%V)) in
        let: "leakB" := (λ: <>, do: "leak" (InjR (InjL #()%V))) in
        let: "leakOut" := (λ: "z", do: "leak" (InjR (InjR "z"))) in
        handle: "f" ("leakA", "leakB", "leakOut") with
    | effect "leak" "p", rec "k" =>
        match: "p" with
        (* Alice gave her input: sample the message to the aggregator *)
        | InjL <> =>
            let: "u" := g^(sample #()%V) in
            "lu" <- SOME "u";;
            "lsAB" alice;;
            "sendAC" "u";;
            "k" #()%V
        | InjR "q" =>
            match: "q" with
            (* Bob wants [r]: forward the env's delivery decision *)
            | InjL <> => "k" ("lrAB" bob)
            (* Bob's input was accepted: complete the output *)
            | InjR "z" =>
                match: !"lu" with
                | NONE => "k" #()%V
                | SOME "u" => "sendBC" ("z" · ("u"^-1));; "k" #()%V
                end
            end
        end
    | return "y" => "y" end.

  Definition R_ADD : expr := F_CHAN ∘F π_ADD.

  Definition I_ADD : expr := S_ADD ∘f F_ADD.

End secure_add.

Section secure_add_type.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.

  (* Both scenarios take a client using the input ports of Alice and Bob,
     and then the aggregator's operations together with the leak operations
     of [F_CHAN]. *)
  Definition τ_ADD : sem_ty Σ :=
    (∀ᵣ θ__L, (∀ᵣ θₕ, ((ℕ -{ θₕ }-> 𝟙) × (ℕ -{ θₕ }-> 𝟙)) -{ sem_row_union θₕ θ__L }-∘ 𝟙) ⊸
       (∀ᵣ θ₁, (((𝔾 -{ θ₁ }-> 𝟙) × (𝔾 -{ θ₁ }-> 𝟙))
                × (((𝟙 + 𝟙) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)))
                 -{ sem_row_union (¡ θ₁)%R θ__L }-∘ 𝟙))%T.

End secure_add_type.
