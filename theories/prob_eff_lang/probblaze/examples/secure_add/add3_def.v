From clutch.prob_eff_lang.probblaze Require Export notation valgroup comp_operators.
From clutch.prob_eff_lang.probblaze Require Import logic sem_types sem_def sem_row.

Import fingroup.
Import valgroup_notation.

(** Three-party secure addition against a passive adversary.

    Party [i] holds [x_i]; all three learn [x₀ · x₁ · x₂] (the group is
    written multiplicatively).  Each party splits its input into three
    shares, sends one share to each peer, sums the shares it holds, sends
    that sum to each peer, and outputs the product of the three sums.

    All functionalities allocate their state once, outside [λ f]: the
    environment may call them repeatedly, each call being one session, and
    acts as the scheduler by setting sessions aside when they wait. *)

Section secure_add3.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* Message tags. *)
  Definition Shr : val := #0.
  Definition Sum : val := #1.

  (* A header [(src, dst, tag)] as a single table key. *)
  Definition hkey : val := λ: "s" "d" "t", #6 * "s" + #2 * "d" + "t".

  (* The [i]-th component of a triple. *)
  Definition sel3 : val :=
    λ: "t" "i",
      let, ("a", "b", "c") := "t" in
      if: "i" = #0 then "a" else if: "i" = #1 then "b" else "c".

  (* Write-once tables: association lists [SOME ((key, v), rest)]. *)
  Definition tbl_lookup : val :=
    rec: "lookup" "l" "key" :=
      match: "l" with
        NONE => NONE
      | SOME "p" =>
          let, ("e", "rest") := "p" in
          let, ("k", "v") := "e" in
          if: "k" = "key" then SOME "v" else "lookup" "rest" "key"
      end.

  Definition tbl_add : val := λ: "l" "key" "v", SOME (("key", "v"), "l").

  #[local] Notation n := (S n'').

  (* Uniform sampling of an exponent, and of a group element. *)
  Definition sample : expr := λ: <>, rand #n.
  Definition smp : val := λ: <>, g^(sample #()%V).

  (** * Network: secure, authenticated channels between all parties. *)

  (* The network's handling of one request [req], with continuation [k].
     [patch] post-processes every delivered message; the real network uses
     the identity, the simulator's copy corrects one message. *)
  Definition net_handle : val :=
    λ: "patch" "mbox" "netleak" "wait" "req" "k",
      match: "req" with
        InjL "sm" =>
          (* send: store once, leak the header *)
          let, ("s", "msg") := "sm" in
          let, ("d", "t", "m") := "msg" in
          let: "key" := hkey "s" "d" "t" in
          (match: tbl_lookup !"mbox" "key" with
             NONE => "mbox" <- tbl_add !"mbox" "key" "m";; "netleak" ("s", "d", "t")
           | SOME <> => #()%V
           end);;
          "k" #()%V
      | InjR "rh" =>
          (* receive: ask the environment before every attempt *)
          let, ("d", "h") := "rh" in
          let, ("s", "t") := "h" in
          let: "attempt" := (rec: "attempt" <> :=
            "wait" ("s", "d", "t");;
            match: tbl_lookup !"mbox" (hkey "s" "d" "t") with
              NONE => "attempt" #()%V
            | SOME "m" => "patch" "s" "d" "t" "m"
            end) in
          "k" ("attempt" #()%V)
      end.

  (* One session of the network, on the shared mailbox [mbox]. *)
  Definition F_NET_sess : val :=
    λ: "patch" "mbox" "f" "envops",
        let, ("netleak", "wait") := "envops" in
        effect "net"
        let: "ep" := (λ: "i",
          (λ: "msg", do: "net" (InjL ("i", "msg")),
           λ: "h", do: "net" (InjR ("i", "h")))) in
        handle: "f" ("ep" #0, "ep" #1, "ep" #2) with
        | effect "net" "req", rec "k" => net_handle "patch" "mbox" "netleak" "wait" "req" "k"
        | return "y" => "y"
        end.

  Definition F_NET_gen : val :=
    λ: "patch",
      let: "mbox" := ref NONE in
      λ: "f" "envops", F_NET_sess "patch" "mbox" "f" "envops".

  Definition F_NET : expr := (F_NET_gen (λ: "s" "d" "t" "m", "m"))%E.

  (** * Parties *)

  (* Party [i]'s program, given its endpoint and its sampler. *)
  Definition party : val :=
    λ: "i" "x" "ops",
      let, ("ep", "smp") := "ops" in
      let, ("send", "recv") := "ep" in
      let: "p" := ("i" + #1) `rem` #3 in
      let: "q" := ("i" + #2) `rem` #3 in
      let: "r_p" := "smp" #()%V in
      let: "r_q" := "smp" #()%V in
      "send" ("p", Shr, "r_p");;
      "send" ("q", Shr, "r_q");;
      let: "b_p" := "recv" ("p", Shr) in
      let: "b_q" := "recv" ("q", Shr) in
      let: "s" := (("x" · ("r_p" · "r_q")^-1) · "b_p") · "b_q" in
      "send" ("p", Sum, "s");;
      "send" ("q", Sum, "s");;
      let: "s_p" := "recv" ("p", Sum) in
      let: "s_q" := "recv" ("q", Sum) in
      ("s" · "s_p") · "s_q".

  (* Passive corruption: leak the party's randomness and the messages it
     receives. *)
  Definition leaky : val :=
    λ: "leak" "ops",
      let, ("ep", "smp") := "ops" in
      let, ("send", "recv") := "ep" in
      (("send", λ: "h", let: "m" := "recv" "h" in "leak" (InjR ("h", "m"));; "m"),
       λ: <>, let: "r" := "smp" #()%V in "leak" (InjL "r");; "r").

  (* Run party [i] on input [x], over the network endpoints [eps]; party [c]
     is corrupt and leaks through [leak]. *)
  Definition run_party (c : nat) : val :=
    λ: "leak" "eps" "i" "x",
      let: "ep" := sel3 "eps" "i" in
      let: "ops" := (if: "i" = #c then leaky "leak" ("ep", smp) else ("ep", smp)) in
      party "i" "x" "ops".

  (* One session of the protocol with party [c] corrupted.  Port [i] runs
     party [i]'s program, at most once overall (tracked by [started]). *)
  Definition Π_sess (c : nat) : val :=
    λ: "started" "f" "r",
      let, ("leak", "eps") := "r" in
      effect "go"
      let: "port" := (λ: "i" "x", do: "go" ("i", "x")) in
      handle: "f" ("port" #0, "port" #1, "port" #2) with
      | effect "go" "ix", rec "k" =>
          let, ("i", "x") := "ix" in
          match: vg_of_int "x" with
            NONE => "k" NONE
          | SOME "x" =>
              let: "st" := sel3 "started" "i" in
              if: !"st" then "k" NONE else
                "st" <- #true;;
                "k" (SOME (run_party c "leak" "eps" "i" "x"))
          end
      | return "y" => "y"
      end.

  Definition Π (c : nat) : expr :=
    let: "started" := (ref #false, ref #false, ref #false) in
    λ: "f" "r", Π_sess c "started" "f" "r".

  Definition R_ADD3 (c : nat) : expr := functionality_composition F_NET (Π c).

  (** * Ideal world *)

  (* The product of the inputs, once all are in. *)
  Definition prod3 : val :=
    λ: "xs",
      let, ("x0", "x1", "x2") := "xs" in
      match: !"x0" with
        NONE => NONE
      | SOME "a" =>
          match: !"x1" with
            NONE => NONE
          | SOME "b" =>
              match: !"x2" with NONE => NONE | SOME "c" => SOME (("a" · "b") · "c") end
          end
      end.

  (* One session of the ideal functionality, on the inputs [xs]. *)
  Definition F_ADD3_sess (c : nat) : val :=
    λ: "xs" "f" "leakIn",
      effect "go"
      let: "port" := (λ: "i" "x", do: "go" ("i", "x")) in
      handle: "f" ("port" #0, "port" #1, "port" #2) with
      | effect "go" "ix", rec "k" =>
          let, ("i", "x") := "ix" in
          match: vg_of_int "x" with
            NONE => "k" NONE
          | SOME "x" =>
              let: "xi" := sel3 "xs" "i" in
              match: !"xi" with
                SOME <> => "k" NONE
              | NONE =>
                  "xi" <- SOME "x";;
                  (* S learns c's input, and the output once all inputs are in *)
                  "leakIn" ("i", (if: "i" = #c then SOME "x" else NONE), prod3 "xs");;
                  "k" (prod3 "xs")
              end
          end
      | return "y" => "y"
      end.

  Definition F_ADD3 (c : nat) : expr :=
    let: "xs" := (ref NONE, ref NONE, ref NONE) in
    λ: "f" "leakIn", F_ADD3_sess c "xs" "f" "leakIn".

  (* The honest party whose final message to [c] the simulator corrects. *)
  Definition hon (c : nat) : nat := (c + 1) mod 3.

  (* The simulator's patch: [hon c]'s sum to [c] is multiplied by [!δ]. *)
  Definition patch (c : nat) : val :=
    λ: "δ" "s" "d" "t" "m",
      if: ("s" = #(hon c)) && ("d" = #c) && ("t" = Sum) then "m" · !"δ" else "m".

  (* What the simulator does when F_ADD3 reports that party [i] gave its
     input: record [x_c] and [δ = y · x_c⁻¹] when known, and run party [i]
     itself, on the dummy input 1 if it is honest. *)
  Definition sim_leak (c : nat) : val :=
    λ: "δ" "xc" "leak" "eps" "e",
      let, ("i", "xo", "yo") := "e" in
      (match: "xo" with NONE => #()%V | SOME "x" => "xc" <- "x" end);;
      (match: "yo" with NONE => #()%V | SOME "y" => "δ" <- ("y" · (!"xc")^-1) end);;
      let: "x" := (match: "xo" with NONE => vunit | SOME "x" => "x" end) in
      run_party c "leak" "eps" "i" "x";; #()%V.

  (* The simulator runs its own copy of the real protocol, on its own
     network; honest parties get the dummy input 1, and [hon c]'s sum to
     [c] is patched so that [c]'s view is consistent with the output.  Like
     the real world, it runs one network session per session of the
     environment. *)
  Definition S_ADD3 (c : nat) : expr :=
    let: "δ" := ref vunit in
    let: "xc" := ref vunit in
    functionality_composition
      (F_NET_gen (patch c "δ"))
      (λ: "g" "r",
         let, ("leak", "eps") := "r" in
         "g" (sim_leak c "δ" "xc" "leak" "eps")).

  Definition I_ADD3 (c : nat) : expr := func_comp (S_ADD3 c) (F_ADD3 c).

End secure_add3.

Section secure_add3_type.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.

  (* A party's port: it takes the input as a number and returns the
     party's output. *)
  Definition τ_port (θ : sem_row Σ) : sem_ty Σ := (sem_ty_nat -{ θ }-> Option 𝔾)%T.

  (* A message header [(src, dst, tag)]. *)
  Definition τ_hdr : sem_ty Σ := ((ℤ × ℤ) × ℤ)%T.

  (* What the corrupt party leaks: a sample [Rnd r], or a received message
     [Rcv ((src, tag), m)]. *)
  Definition τ_view : sem_ty Σ := (𝔾 + ((ℤ × ℤ) × 𝔾))%T.

  (* The environment's operations: the corrupt party's leak, and the
     network's [netleak] (on every first send) and [wait] (before every
     receive attempt). *)
  Definition τ_envops (θ : sem_row Σ) : sem_ty Σ :=
    ((τ_view -{ θ }-> 𝟙) × ((τ_hdr -{ θ }-> 𝟙) × (τ_hdr -{ θ }-> 𝟙)))%T.

  (* Both worlds.  The scenario can be called any number of times; each call
     is one session, in which the client uses the three ports and returns a
     result of its choice. *)
  Definition τ_ADD3 : sem_ty Σ :=
    (![MS] (∀ₜ α, ∀ᵣ θ__L,
       (∀ᵣ θₕ, ((τ_port θₕ × τ_port θₕ) × τ_port θₕ) -{ sem_row_union θₕ θ__L }-∘ α) ⊸
       (∀ᵣ θ₁, τ_envops θ₁ -{ sem_row_union (¡ θ₁)%R θ__L }-∘ α)))%T.

End secure_add3_type.
