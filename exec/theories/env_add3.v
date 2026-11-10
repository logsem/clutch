(** * Environments for three-party secure addition ([add3_def])

    The environment is the scheduler.  It calls the system once to get an
    instance and starts three sessions on it, one per party.  The network
    asks the environment ([wait]) before every receive attempt; the
    environment then suspends the session by performing its own effect
    [w], whose handler returns the session's continuation, and resumes the
    suspended sessions round-robin.  This is the pattern of
    [scheduler_typed.Zsched]. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup add3_def.
From clutch_exec Require Import exec_common.

Section env_add3.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Import valgroup_notation.

  (** Run three parties on the inputs [xs = (x0, x1, x2)] (indices), with
      at most [fuel] scheduling rounds; the outputs are left in [out].
      [onleak] receives the corrupt party's leaks. *)
  Definition add3_schedule (obs : string → val) (xs onleak out fuel : expr) : expr :=
    (effect "w"
     let: "inst" := "X" #()%V in
     let: "ports" := ((λ: "l", (obs "leak") "l" ;; onleak "l"),
                      ((λ: "h", (obs "netleak") "h"),
                       (λ: "h", (obs "wait") "h" ;; do: "w" #()%V))) in
     let: "start" := (λ: "i",
       handle: "inst" (λ: "ps", (sel3 out "i") <- (sel3 "ps" "i") (sel3 xs "i")) "ports" with
       | effect "w" <>, rec "k" => InjR "k"
       | return <> => InjL #()%V
       end) in
     let: "step" := (λ: "s", match: "s" with InjL <> => InjL #()%V | InjR "k" => "k" #()%V end) in
     let: "done" := (λ: "s", match: "s" with InjL <> => #true | InjR <> => #false end) in
     let: "s0" := "start" #0 in
     let: "s1" := "start" #1 in
     let: "s2" := "start" #2 in
     (rec: "loop" "fuel" "s0" "s1" "s2" :=
        if: ("done" "s0") && ("done" "s1") && ("done" "s2") then #()%V
        else if: "fuel" ≤ #0 then (obs "out of fuel") #()%V
        else
          let: "s0" := "step" "s0" in
          let: "s1" := "step" "s1" in
          let: "s2" := "step" "s2" in
          "loop" ("fuel" - #1) "s0" "s1" "s2") fuel "s0" "s1" "s2")%E.

  (** Honest run: true iff all three parties output the product of the
      inputs. *)
  Definition env_add3_honest (x0 x1 x2 : Z) (obs : string → val) : val :=
    λ: "X",
      let: "xs" := (#x0, #x1, #x2) in
      let: "out" := (ref NONE, ref NONE, ref NONE) in
      add3_schedule obs "xs" (λ: <>, #()%V) "out" #100 ;;
      let, ("o0", "o1", "o2") := "out" in
      (obs "outputs") (!"o0", !"o1", !"o2") ;;
      match: vg_of_int #x0 with NONE => #false | SOME "a" =>
      match: vg_of_int #x1 with NONE => #false | SOME "b" =>
      match: vg_of_int #x2 with NONE => #false | SOME "c" =>
        let: "y" := ("a" · "b") · "c" in
        let: "ok" := (λ: "o", match: !"o" with NONE => #false | SOME "z" => veq "z" "y" end) in
        "ok" "o0" && "ok" "o1" && "ok" "o2"
      end end end.

  (** True iff the first message the corrupt party receives is the unit.
      Its view is the same in both worlds. *)
  Definition env_add3_peek (x0 x1 x2 : Z) (obs : string → val) : val :=
    λ: "X",
      let: "xs" := (#x0, #x1, #x2) in
      let: "out" := (ref NONE, ref NONE, ref NONE) in
      let: "first" := ref NONE in
      add3_schedule obs "xs"
        (λ: "l", match: "l" with
                   InjL <> => #()%V
                 | InjR "hm" =>
                     let, ("h", "m") := "hm" in
                     match: !"first" with NONE => "first" <- SOME "m" | SOME <> => #()%V end
                 end) "out" #100 ;;
      match: !"first" with NONE => #false | SOME "m" => veq "m" vunit end.
End env_add3.
