(* Functional correctness of the secure channel over DHKE: delivery.

   A client that only schedules through [ssend]/[srecv] while answering the
   leaks honestly never gets a message through [REAL_DHKE_CHAN]: Alice's
   first key request needs Bob's reply, and Bob only runs when the client
   receives.  Correctness only asks that the message arrives under SOME
   scheduler, and the natural one is the honest network: when [F_AUTH] leaks
   Alice's share, Bob is activated before the leak returns, by a nested call
   of the same session whose client performs one [srecv].

   [sched_prog mz] runs the session against this scheduler with the client
   "send [mz]; receive and record".  [sched_prog_delivers] runs it on the
   right-hand side of the relational logic against a trivial left program,
   so that every execution, including the two random samples of the key
   exchange, ends with the received value equal to the sent message.
   [dhke_chan_delivers] is the consequence for the distribution of the
   program: with probability one it terminates and returns the message.

   Finally, [sched] is shown syntactically well-typed at the interface of
   [REAL_DHKE_CHAN] used in the security proof, and plugged into
   [dhke_chan_realises_typed]. *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory mode adequacy valgroup.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze.examples Require Import mask sec_channel_def advantage_dhke_sec_channel.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.
Import valgroup_tactics.

#[local] Open Scope factory_scope.

Section scheduler.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {msk : @Mask (@vgG vg) vgval}.

  (* The honest answers to the leaks.  The channel's leaks (the first pair)
     answer a receive with [() + ()], those of the key exchange (the second
     pair) with [() + ℕ]. *)
  Definition leak_send : val := (λ: "x", #()%V)%V.
  Definition leak_recv_c : val := (λ: "x", SOME #()%V)%V.
  Definition leak_recv_k : val := (λ: "x", SOME #0)%V.
  Definition honest_leaks : val :=
    ((leak_send, leak_recv_c), (leak_send, leak_recv_k))%V.

  (* The nested client activates Bob: it receives once. *)
  Definition nested_client : val :=
    (λ: "ops", let, ("ssend", "srecv") := "ops" in "srecv" #()%V ;; #()%V)%V.

  (* The scheduler, an environment: it takes the factory of the system,
     creates one session [sys], and re-enters it with the nested client and
     honest leaks when Alice's message is leaked.  The main client sends [mz],
     receives, and hands what it got to the environment by raising [out],
     which the environment's handler turns into the result. *)
  Definition sched (mz : nat) : val :=
    (λ: "f",
      let: "sys" := "f" #()%V in
      let: "scheduler" := (λ: "x", "sys" nested_client honest_leaks) in
      effect "out"
        handle: "sys" (λ: "ops", let, ("ssend", "srecv") := "ops" in
                         "ssend" #mz ;; do: "out" ("srecv" #()%V))
                      ((leak_send, leak_recv_c), ("scheduler", leak_recv_k)) with
        | effect "out" "v", rec "k" => "v"
        | return "y" => NONEV
        end)%V.

  Definition sched_prog (mz : nat) : expr := sched mz REAL_DHKE_CHAN.

End scheduler.

(* Apply a right-side rule stated over [fill K] to the next redex of the
   right program. *)
Tactic Notation "brel_focus_r" open_constr(sub) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (brel _ _ ?er _ _) =>
      let k := eq_find_ctx er sub in change er with (fill k sub)
  end.
Ltac pr := try (try brel_pures_r).

(* Handle the effect raised under the explicit inner context [K']
   (innermost frame first): its handler is the nearest one for that label. *)
Tactic Notation "brel_handle_r_in" constr(l) open_constr(K') :=
  brel_focus_r (Handle _ OS (EffLabel l) (fill K' (Do (EffLabel l) (Val _))) _ _);
  iApply (brel_handle_os_r _ K').

(* The label side condition of a handler step. *)
Ltac lab_side :=
  match goal with
  | Hn : NoDup _ |- _ =>
      let H := fresh "H" in pose proof Hn as H; rewrite !NoDup_cons in H;
      repeat match goal with H' : _ ∧ _ |- _ => destruct H' end;
      unfold ectx_labels; simpl; set_solver
  end.

Tactic Notation "bh" constr(l) open_constr(K') "as" simple_intropattern(r) constr(H) :=
  brel_handle_r_in l K'; [ lab_side | iIntros (r) H ].

(* Frames are listed outermost first: the context inside the handler for
   [l] is the part of [K] after its handler frame. *)
Ltac split_at_label l K :=
  lazymatch K with
  | HandleCtx _ _ l _ _ :: ?K2 => constr:(K2)
  | _ :: ?K2 => split_at_label l K2
  end.

(* Handle the next [do:] of the right program by its nearest handler. *)
Tactic Notation "bha" simple_intropattern(r) constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (brel _ _ ?er _ _) =>
      let sub := open_constr:(Do (EffLabel _) (Val _)) in
      let Kall := eq_find_ctx er sub in
      lazymatch sub with
      | Do (EffLabel ?l) _ =>
          let K' := split_at_label l Kall in
          brel_handle_r_in l K'; [ lab_side | iIntros (r) H ]
      end
  end.

Section proof.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {msk : @Mask (@vgG vg) vgval} `{!Mask_struc}.

  Lemma brel_learn_nodup e1 e2 l1s l2s L R :
    (⌜NoDup l1s ∧ NoDup l2s⌝ -∗ BREL e1 ≤ e2 <|(l1s, l2s, iThyBot) :: L|> {{R}})
    ⊢ BREL e1 ≤ e2 <|(l1s, l2s, iThyBot) :: L|> {{R}}.
  Proof.
    iIntros "H". iApply brel_learn. iIntros ([Hdl Hdr]) "_".
    apply distinct_l_cons_inv in Hdl as [Hl _]. apply distinct_r_cons_inv in Hdr as [Hr _].
    iApply "H". iPureIntro. split; done.
  Qed.

  Lemma sched_prog_delivers (mz : nat) (m : vgG) :
    vg_of_int_sem mz = Some m →
    ⊢ BREL #()%V ≤ sched_prog mz <|⊥|> {{ λ _ v, ⌜v = SOMEV (vgval m)⌝ }}.
  Proof using All.
    intros Hmz.
    rewrite /sched_prog /sched /REAL_DHKE_CHAN /nested_client /honest_leaks /leak_send /leak_recv_c /leak_recv_k.
    iApply brel_new_theory.
    brel_pures_r.
    brel_alloc_r l_cmsg as "Hl_cmsg". brel_pures_r.
    brel_alloc_r l_omsg as "Hl_omsg". brel_pures_r.
    brel_alloctape_r α as "Hα". brel_pures_r.
    brel_alloctape_r β as "Hβ". brel_pures_r.
    rewrite Nat2Z.id.
    iDestruct (empty_to_spec_tapeN with "Hα") as "Hα".
    iDestruct (empty_to_spec_tapeN with "Hβ") as "Hβ".
    brel_alloc_r l1 as "Hl1". brel_pures_r.
    brel_alloc_r l2 as "Hl2". brel_pures_r.
    brel_alloc_r m1 as "Hm1". brel_pures_r.
    brel_alloc_r m2 as "Hm2". brel_pures_r.
    brel_effect_r l_out as "Hl_out". try (try brel_pures_r).
    brel_effect_r l_as as "Hl_as". try (try brel_pures_r).
    brel_effect_r l_ar as "Hl_ar". try (try brel_pures_r).
    brel_effect_r l_gk as "Hl_gk". try (try brel_pures_r).
    brel_effect_r l_os as "Hl_os". try (try brel_pures_r).
    brel_effect_r l_or as "Hl_or". try (try brel_pures_r).
    brel_effect_r l_ss as "Hl_ss". try (try brel_pures_r).
    brel_effect_r l_sr as "Hl_sr". try (try brel_pures_r).
    iApply (brel_add_label_r with "Hl_out").
    iApply (brel_add_label_r with "Hl_as").
    iApply (brel_add_label_r with "Hl_ar").
    iApply (brel_add_label_r with "Hl_gk").
    iApply (brel_add_label_r with "Hl_os").
    iApply (brel_add_label_r with "Hl_or").
    iApply (brel_add_label_r with "Hl_ss").
    iApply (brel_add_label_r with "Hl_sr").
    iApply brel_learn_nodup. iIntros "%Hnd". destruct Hnd as [_ Hnd].
    (* the client's [ssend] reaches CHAN's handler *)
    bh l_ss [AppRCtx _] as r1 "Hr1". pr.
    brel_focus_r (vg_of_int #_)%E.
    iApply brel_vg_of_int_correct_r; first exact Hmz. pr.
    brel_load_r. pr.
    brel_store_r. pr.
    bha r2 "Hr2". pr.
    brel_load_r. pr.
    brel_focus_r (rand(#lbl:α) #_)%E.
    iApply brel_randT_empty_r.
    iSplitL "Hα"; first (iNext; iExact "Hα").
    iIntros (a) "Hα %Ha". pr.
    brel_store_r. pr.
    brel_exp_r. pr.
    bha r3 "Hr3". pr.
    brel_load_r. pr.
    brel_store_r. pr.
    (* the leak of Alice's message runs the scheduler: a nested call *)
    brel_effect_r n_as as "Hn_as". try (try brel_pures_r).
    brel_effect_r n_ar as "Hn_ar". try (try brel_pures_r).
    brel_effect_r n_gk as "Hn_gk". try (try brel_pures_r).
    brel_effect_r n_os as "Hn_os". try (try brel_pures_r).
    brel_effect_r n_or as "Hn_or". try (try brel_pures_r).
    brel_effect_r n_ss as "Hn_ss". try (try brel_pures_r).
    brel_effect_r n_sr as "Hn_sr". try (try brel_pures_r).
    iApply (brel_add_label_r with "Hn_as").
    iApply (brel_add_label_r with "Hn_ar").
    iApply (brel_add_label_r with "Hn_gk").
    iApply (brel_add_label_r with "Hn_os").
    iApply (brel_add_label_r with "Hn_or").
    iApply (brel_add_label_r with "Hn_ss").
    iApply (brel_add_label_r with "Hn_sr").
    clear Hnd.
    iApply brel_learn_nodup. iIntros "%Hnd". destruct Hnd as [_ Hnd].
    (* the nested client receives *)
    bha n1 "Hn1". pr.
    (* nested Bob: getKey alice, receiving Alice's share from m1 *)
    bha n2 "Hn2". pr.
    bha n3 "Hn3". pr.
    brel_load_r. pr.
    brel_cont_r. pr.
    brel_load_r. pr.
    brel_focus_r (rand(#lbl:β) #_)%E.
    iApply brel_randT_empty_r.
    iSplitL "Hβ"; first (iNext; iExact "Hβ").
    iIntros (b) "Hβ %Hb". pr.
    brel_store_r. pr.
    brel_exp_r. pr.
    bha n4 "Hn4". pr.
    brel_load_r. pr.
    brel_store_r. pr.
    brel_cont_r. pr.
    brel_exp_r. pr.
    brel_cont_r. pr.
    (* nested CHAN: the F_OAUTH receive finds no message yet *)
    bha n5 "Hn5". pr.
    brel_load_r. pr.
    brel_cont_r. pr.
    brel_cont_r. pr.
    (* back in Alice's call: the leak returned; Alice reads Bob's share *)
    brel_cont_r. pr.
    bha r4 "Hr4". pr.
    brel_load_r. pr.
    brel_cont_r. pr.
    brel_exp_r. pr.
    brel_cont_r. pr.
    brel_focus_r (App (App (Val mask.mask) _) _).
    iApply mask_correct_r. pr.
    bha r5 "Hr5". pr.
    brel_load_r. pr.
    brel_store_r. pr.
    brel_cont_r. pr.
    brel_cont_r. pr.
    (* the client receives: Bob's branch again, now with l2 and m2 filled *)
    bha s1 "Hs1". pr.
    bha s2 "Hs2". pr.
    bha s3 "Hs3". pr.
    brel_load_r. pr.
    brel_cont_r. pr.
    brel_load_r. pr.
    brel_exp_r. pr.
    bha s4 "Hs4". pr.
    brel_load_r. pr.
    brel_cont_r. pr.
    brel_exp_r. pr.
    brel_cont_r. pr.
    bha s5 "Hs5". pr.
    brel_load_r. pr.
    brel_cont_r. pr.
    brel_focus_r (App (App (Val mask.mask) _) _).
    iApply mask_correct_r. pr.
    brel_cont_r. pr.
    bha ro "Hro". pr.
    rewrite (expgAC g a b) (mask_involutive _ m).
    iModIntro. done.
  Qed.

End proof.

Section adequacy.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  (* The scheduler delivers: the run terminates with the sent message as
     the received value, in the coupling with the trivial program. *)
  Theorem dhke_chan_delivers_coupling (mz : nat) (m : vgG) (σ σ' : state) :
    (∀ `{!probblazeRGS Σ}, vg_of_int_sem mz = Some m) →
    ARcoupl (lim_exec (Val #()%V, σ)) (lim_exec (sched_prog mz, σ'))
      (λ _ v, v = SOMEV (vgval m)) 0.
  Proof using All.
    intros Hmz.
    apply (brel_refines_coupling Σ (λ _, λ _ v, ⌜v = SOMEV (vgval m)⌝%I)
             (λ _ v, v = SOMEV (vgval m))).
    - intros ? v v'. iIntros "%H". done.
    - intros ?. iApply sched_prog_delivers. apply Hmz.
  Qed.

  (* With probability one, the scheduled run of the channel over DHKE
     terminates and returns the message that was sent. *)
  Corollary dhke_chan_delivers (mz : nat) (m : vgG) (σ : state) :
    (∀ `{!probblazeRGS Σ}, vg_of_int_sem mz = Some m) →
    lim_exec (sched_prog mz, σ) (SOMEV (vgval m)) = 1.
  Proof using All.
    intros Hmz.
    pose proof (dhke_chan_delivers_coupling mz m σ σ Hmz) as Hc.
    rewrite (lim_exec_final (Val #()%V, σ) #()%V) in Hc; last done.
    set (t := SOMEV (vgval m)).
    specialize (Hc (λ _, 1) (λ b, if bool_decide (b = t) then 1 else 0)).
    assert (SeriesC (λ a, dret #()%V a * 1) = 1) as Hl.
    { rewrite (SeriesC_ext _ (λ a, if bool_decide (a = #()%V) then 1 else 0)).
      - apply SeriesC_singleton.
      - intros a. rewrite dret_pmf_unfold /dret_pmf. case_bool_decide; lra. }
    assert (SeriesC (λ b, lim_exec (sched_prog mz, σ) b *
                          (if bool_decide (b = t) then 1 else 0)) =
            lim_exec (sched_prog mz, σ) t) as Hr.
    { rewrite (SeriesC_ext _ (λ b, if bool_decide (b = t)
                  then lim_exec (sched_prog mz, σ) t else 0)).
      - apply SeriesC_singleton.
      - intros b. destruct (decide (b = t)) as [->|Hb].
        + rewrite !bool_decide_eq_true_2 //. ring.
        + rewrite !bool_decide_eq_false_2 //. ring. }
    rewrite Hl Hr in Hc.
    assert (1 <= lim_exec (sched_prog mz, σ) t + 0) as H1.
    { apply Hc.
      - intros; lra.
      - intros b. case_bool_decide; lra.
      - intros a b Hab. case_bool_decide; [lra|]. exfalso. by apply H.
      }
    pose proof (pmf_le_1 (lim_exec (sched_prog mz, σ)) t). lra.
  Qed.

End adequacy.

(* ------------------------------------------------------------------ *)
(* The scheduler is a syntactically typed environment.                 *)
(* ------------------------------------------------------------------ *)

(* [sched mz] takes the factory of the system and returns the received value,
   so that it has the type [(() -∘ T_DHKE_CHAN) ⇾ (() + τG)], the interface
   of [REAL_DHKE_CHAN] used for the security proof.  Composed with a final
   test of the result it is an environment of [dhke_chan_realises_typed]. *)

From Autosubst Require Import Autosubst.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics.
From clutch.prob_eff_lang.probblaze.typing Require Import types.
From clutch.prob_eff_lang.probblaze.examples Require Import scheduler_typed.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From Stdlib Require Import Reals Psatz.
From iris.algebra Require Import excl frac.
From iris.algebra.lib Require Import dfrac_agree.

Section sched_typed.
  Context {cg : clutch_group_struct}.
  (* The type of group elements has no free row variables; this is what
     instantiating the row variables of [T_DHKE_CHAN] needs. *)
  Context (τG_cl : ∀ σ : var → row, τG.|[σ] = τG).
  Context (τG_clt : ∀ σ : var → type, τG.[σ] = τG).
  (* and mentions no effect names, so that any name is fresh for it. *)
  Context (τG_nm : ∀ s : string, s ∉ vars._ty τG).

  Local Notation TD := (T_DHKE_CHAN (cg:=cg)).

  Lemma TD_nm (s : string) : s ∉ vars._ty TD.
  Proof using cg τG_cl τG_clt τG_nm. rewrite /T_DHKE_CHAN /=. pose proof (τG_nm s). set_solver. Qed.

  (* [TD] is duplicable: a session may be used any number of times. *)
  Lemma TD_multi : le.MultiT TD.
  Proof.
    rewrite /le.MultiT /T_DHKE_CHAN /=. eapply le.TTrans_le;
      [apply le.TForallR_le, le.TBangIdemp1_le|apply le.TBangTForallRComm2_le].
  Qed.

  (* The pieces of [T_DHKE_CHAN = ∀R: (Acl ⇾ Bcl)], with row variable 0 the
     row of the client of the channel. *)
  Definition Ops : type :=
    ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> (() + τG)))%ty.
  Definition Acl : type := (∀R: Ops -{ RUnion (RVar 0%nat) (RVar 1%nat) }-∘ ())%ty.
  Definition Lk : type :=
    ((((τG * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> (() + ())))
      * (((τG * (() + ())) -{ RVar 0%nat }-> ()) * ((() + ()) -{ RVar 0%nat }-> (() + ℕ)))
      -{ RUnion (RFlip OS (RVar 1%nat)) (RUnion (RFlip OS (RVar 0%nat)) (RVar 2%nat)) }-∘ ())%ty.
  Definition Bcl : type := (∀R: ∀R: Lk)%ty.

  Lemma TD_eq : TD = (∀R: (Acl ⇾ Bcl))%ty.
  Proof. reflexivity. Qed.

  (* The row of a call of the session whose two leak interfaces have empty
     rows is the row of the client. *)
  Lemma row_call_nil D b (ρ : row) :
    D ⊢ₗ RUnion (RFlip OS RNil) (RUnion (RFlip OS RNil) ρ) ≤R ρ @ b.
  Proof.
    eapply le.RTrans_le.
    { apply le.RUnion_le; first apply le.RFlipNil_le.
      apply le.RUnion_le; [apply le.RFlipNil_le|apply RRefl_le]. }
    eapply le.RTrans_le; apply le.RUnionNilRight2_le.
  Qed.

  (* The honest leaks, as values of the types of the leak interfaces. *)
  Lemma leak_send_typed : ⊢ᵥ leak_send : ((τG * (() + ())) ⇾ ())%ty.
  Proof.
    apply Rec_val_typed; first done. simpl.
    eapply (Sub_typed _ _ _ [] _ _ RNil false _ ()%ty);
      [apply CRefl_le|exact I|apply RRefl_le|apply le.TRefl_le|apply Val_typed; constructor].
  Qed.

  Lemma leak_recv_c_typed : ⊢ᵥ leak_recv_c : ((() + ()) ⇾ (() + ()))%ty.
  Proof.
    apply Rec_val_typed; first done. simpl.
    eapply (Sub_typed _ _ _ [] _ _ RNil false _ (() + ())%ty);
      [apply CRefl_le|exact I|apply RRefl_le|apply le.TRefl_le|].
    apply InjR_typed. apply Val_typed. constructor.
  Qed.

  Lemma leak_recv_k_typed : ⊢ᵥ leak_recv_k : ((() + ()) ⇾ (() + ℕ))%ty.
  Proof.
    apply Rec_val_typed; first done. simpl.
    eapply (Sub_typed _ _ _ [] _ _ RNil false _ (() + ℕ)%ty);
      [apply CRefl_le|exact I|apply RRefl_le|apply le.TRefl_le|].
    apply InjR_typed. apply Val_typed. apply (Nat_val_typed 0).
  Qed.

  Lemma honest_leaks_typed :
    ⊢ᵥ honest_leaks : ((((τG * (() + ())) ⇾ ()) * ((() + ()) ⇾ (() + ())))
                        * (((τG * (() + ())) ⇾ ()) * ((() + ()) ⇾ (() + ℕ))))%ty.
  Proof.
    unfold honest_leaks.
    apply Pair_val_typed; apply Pair_val_typed;
      [apply leak_send_typed|apply leak_recv_c_typed|apply leak_send_typed|apply leak_recv_k_typed].
  Qed.

  Lemma multi_bang (X : type) : le.MultiT (![MS] X)%ty.
  Proof. apply le.TBangIdemp1_le. Qed.

  Lemma typed_row_bot Δ Γ e (ρ : row) τ Γ' :
    Δ .| Γ ⊢ₜ e : RNil : τ ⊣ Γ' → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ'.
  Proof.
    intros He.
    eapply (Sub_typed _ _ Γ _ Γ' _ RNil true _ τ);
      [apply CRefl_le|apply CRefl_le|apply le.RBot_le|apply le.TRefl_le|done].
  Qed.

  (* Call a function variable [f : τ -{ρa}-> κ] at the row [ρ]; [f] is consumed. *)
  Lemma typed_call_row Δ Γ1 Γ2 (f : string) e (ρ ρa : row) τ κ :
    le.row_to_disj_ctx ρ ⊢ₗ ρa ≤R ρ @ true → ρa R⪯C Γ2 →
    Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ ((f, (τ -{ ρa }-> κ)%ty) :: Γ2) →
    Δ .| Γ1 ⊢ₜ App (Var f) e : ρ : κ ⊣ Γ2.
  Proof.
    intros Hρ HC He.
    eapply (App_typed _ _ _ _ _ _ ρ RNil ρa true τ κ);
      [apply le.RBot_le|exact Hρ|once_nil|exact HC|exact He|].
    eapply (Sub_typed _ _ _ _ Γ2 _ RNil false _ (τ -{ ρa }-> κ)%ty);
      [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|apply Var_typed].
  Qed.

  Lemma nested_client_typed : ⊢ᵥ nested_client : Acl.|[RNil/].
  Proof using cg τG_cl τG_clt.
    unfold Acl, Ops. asimpl. rewrite ?τG_cl.
    apply RAbs_val_typed.
    eapply (Sub_val_typed _ _ (((ℕ -{ RVar 0 }-> ()) * (() -{ RVar 0 }-> () + τG)) -{ RVar 0 }-[OS]-> ())%ty).
    { eapply le.TTrans_le; first apply le.TBangElim_le.
      eapply (le.TArrow_le _ _ _ _ _ _ _ true);
        [apply le.TRefl_le|apply le.RUnionNilLeft1_le|apply le.TRefl_le]. }
    apply Rec_val_typed; first done. simpl.
    eapply (LetPair_typed _ [("ops", ((ℕ -{ RVar 0 }-> ()) * (() -{ RVar 0 }-> () + τG))%ty)] [] []
              "ssend" "srecv" _ _ (RVar 0) (ℕ -{ RVar 0 }-> ())%ty (() -{ RVar 0 }-> () + τG)%ty ()%ty).
    { solve_fresh. } { solve_fresh. } { solve_fresh. } { solve_fresh. }
    { by intros H; inversion H. }
    { apply typed_row_bot. apply Var_typed. }
    simpl.
    eapply (Let_typed _ _ [("ssend", (ℕ -{ RVar 0 }-> ())%ty)] _ BAnon _ _ (RVar 0)
              (() + τG)%ty ()%ty); [solve_fresh|solve_fresh| |].
    { (* srecv () *)
      eapply typed_perm; first apply perm_swap.
      eapply typed_call_row; [apply RRefl_le| |].
      { apply (le.ConsR_le (RVar 0) "ssend" (ℕ -{ RVar 0 }-> ())%ty []);
          [apply le.Multi_le, multi_bang|apply le.NilR_le]. }
      { apply typed_row_bot. apply Val_typed. constructor. } }
    { (* the result is unit; the unused [ssend] is dropped *)
      eapply (Sub_typed _ _ _ [] _ _ RNil true _ ()%ty);
        [apply CRefl_le|exact I|apply le.RBot_le|apply le.TRefl_le|apply Val_typed; constructor]. }
  Qed.

  (* Call a one-shot function variable on a value; the variable is consumed. *)
  Lemma typed_app_var_val Δ Γ (f : string) (v : val) τ κ :
    ⊢ᵥ v : τ →
    Δ .| (f, (τ -∘ κ)%ty) :: Γ ⊢ₜ App (Var f) (Val v) : RNil : κ ⊣ Γ.
  Proof.
    intros Hv.
    eapply (App_typed _ _ _ _ _ _ _ RNil RNil true τ κ);
      [apply RRefl_le|apply RRefl_le|once_nil|apply RNil_le_ctx|apply Val_typed, Hv|apply Var_typed].
  Qed.

  (* The main client of [sched], as an expression of its own. *)
  Definition main_client (mz : nat) : expr :=
    (λ: "ops", let, ("ssend", "srecv") := "ops" in
       "ssend" #mz ;; do: "out" ("srecv" #()%V))%E.

  (* The row of the client in the main call: it may raise [out]. *)
  Definition ρout : row := RCons (SFlip syntax.OS (SSig "out" (() + τG)%ty ()%ty)) RNil.

  Lemma main_client_typed Δ Γ (mz : nat) :
    Δ !! "out" = Some () →
    Δ .| Γ ⊢ₜ main_client mz : RNil : Acl.|[ρout/] ⊣ Γ.
  Proof using cg τG_cl τG_clt.
    intros Hout. unfold main_client.
    (* first the client at the type with the one-shot arrow, in the row of its
       body: the effect [out] and the row of its operations *)
    eapply (Sub_typed _ _ Γ _ Γ _ RNil true _
              (∀R: (Ops -{ RCons (SFlip syntax.OS (SSig "out" (() + τG)%ty ()%ty)) (RVar 0) }-[OS]-> ()))%ty).
    { apply CRefl_le. } { apply CRefl_le. } { apply RRefl_le. }
    { unfold Acl, ρout. asimpl. rewrite ?τG_cl ?τG_clt.
      eapply le.TForallR_le.
      eapply le.TTrans_le; first apply le.TBangElim_le.
      eapply (le.TArrow_le _ _ _ _ _ _ _ true); [apply le.TRefl_le| |apply le.TRefl_le].
      eapply le.RTrans_le; [apply le.RUnionCons1_le|apply le.RUnionComm_le]. }
    apply (Pure_typed _ [] Γ).
    apply RAbs_pure_typed.
    eapply Rec_pure_typed; [apply le.NilM_le|solve_fresh|solve_fresh|].
    simpl.
    eapply (LetPair_typed _ [("ops", Ops)] [] [] "ssend" "srecv" _ _ _ (ℕ -{ RVar 0 }-> ())%ty
              (() -{ RVar 0 }-> () + τG)%ty ()%ty).
    { solve_fresh. } { solve_fresh. } { solve_fresh. } { solve_fresh. }
    { by intros H; inversion H. }
    { apply typed_row_bot. apply Var_typed. }
    simpl.
    eapply (Let_typed _ _ [("srecv", (() -{ RVar 0 }-> () + τG)%ty)] _ BAnon _ _ _ ()%ty ()%ty);
      [solve_fresh|solve_fresh| |].
    { (* ssend #mz *)
      eapply typed_call_row; [apply le.RExtend_le| |].
      { apply (le.ConsR_le (RVar 0) "srecv" (() -{ RVar 0 }-> () + τG)%ty []);
          [apply le.Multi_le, multi_bang|apply le.NilR_le]. }
      { apply typed_row_bot. apply Val_typed. apply (Nat_val_typed mz). } }
    { (* do: out (srecv ()) *)
      simpl.
      eapply (Do_typed _ _ "out" _ (RVar 0) TUnit (() + τG)%ty ()%ty OS _);
        [apply le.NilM_le|exact Hout|].
      simpl. asimpl. rewrite ?τG_clt.
      eapply typed_call_row; [apply le.RExtend_le|apply le.NilR_le|].
      apply typed_row_bot. apply Val_typed. constructor. }
  Qed.

  Lemma sched_typed (mz : nat) : ⊢ᵥ sched mz : ((() -∘ TD) ⇾ (() + τG))%ty.
  Proof using cg τG_cl τG_clt τG_nm.
    unfold sched.
    apply Rec_val_typed; first done. simpl.
    (* let sys := f () *)
    eapply (Let_typed _ _ [] _ _ _ _ _ TD); [solve_fresh|solve_fresh| |].
    { apply typed_app_var_val. constructor. }
    (* let scheduler := λ x, sys nested_client honest_leaks *)
    eapply (Let_typed _ _ [("sys", TD)] _ _ _ _ _ ((τG * (() + ())) ⇾ ())%ty); [solve_fresh|solve_fresh| |].
    { (* the closure may use [sys] again later: duplicate it *)
      apply (Contraction_typed _ _ _ _ _ _ "sys" TD TD_multi).
      eapply (Rec_typed _ [("sys", TD)] [("sys", TD)] BAnon "x" _ syntax.MS RNil
                (τG * (() + ()))%ty ()%ty).
      { apply (le.ConsM_le _ "sys"); [apply le.MS_le, TD_multi|apply le.NilM_le]. }
      { solve_fresh. }
      { solve_fresh. }
      simpl.
      (* the argument is unused *)
      eapply (Weakening_typed _ [("sys", TD)] [] _ RNil _ "x" (τG * (() + ()))%ty).
      eapply (App_typed _ [("sys", TD)] [("sys", TD)] [] _ _ RNil RNil _ true _ ()%ty).
      6: { (* sys nested_client *)
        assert (Hsys : ∅ .| [("sys", TD)] ⊢ₜ Var "sys" : RNil : ((Acl ⇾ Bcl).|[RNil/])%ty ⊣ []).
        { eapply (RAbsElim_typed _ _ _ _ _ RNil (Acl ⇾ Bcl)%ty). apply Var_typed. }
        assert (Hfun : ∅ .| [("sys", TD)] ⊢ₜ Var "sys" : RNil
                         : (Acl.|[RNil/] -{ RNil }-∘ Bcl.|[RNil/])%ty ⊣ []).
        { eapply (Sub_typed _ _ [("sys", TD)] _ [] _ RNil false _ _); 
            [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|exact Hsys]. }
        assert (Hc : ∅ .| [("sys", TD)] ⊢ₜ App (Var "sys") (Val nested_client)
                       : RNil : Bcl.|[RNil/] ⊣ []).
        { eapply (App_typed _ [("sys", TD)] [("sys", TD)] [] _ _ RNil RNil RNil true
                    (Acl.|[RNil/]) (Bcl.|[RNil/]));
            [apply RRefl_le|apply RRefl_le|once_nil|apply RNil_le_ctx| |exact Hfun].
          apply Val_typed. exact nested_client_typed. }
        pose proof (RAbsElim_typed _ _ _ _ _ RNil _ Hc) as H1.
        pose proof (RAbsElim_typed _ _ _ _ _ RNil _ H1) as H2.
        exact H2. }
      { apply RRefl_le. }
      { asimpl. apply row_call_nil. }
      { once_nil. }
      { constructor. }
      { apply Val_typed. asimpl. rewrite ?τG_cl. apply honest_leaks_typed. } }
    (* the effect [out], the handler that turns it into the result *)
    eapply Effect_typed.
    { pose proof (τG_nm "out") as Hn. pose proof (TD_nm "out") as Hd.
      unfold vars._fresh, vars._ctx. simpl. set_solver. }
    eapply (DeepHandle_typed _ [("scheduler", ((τG * (() + ())) ⇾ ())%ty); ("sys", TD)] [] []
              syntax.OS "out" _ _ _ _ _ _ RNil (SAbs "out") TUnit (() + τG)%ty (() + τG)%ty TUnit);
      [first [constructor | done | intros [] | vm_compute; reflexivity] .. | | |].
    3: { (* effect clause: return the payload *)
      simpl. rewrite ?τG_clt.
      eapply (Sub_typed _ _ _ [] _ _ RNil true _ (() + τG)%ty);
        [apply CRefl_le|exact I|apply le.RBot_le|apply le.TRefl_le|apply Var_typed]. }
    2: { (* return clause: no result *)
      eapply (Sub_typed _ _ _ [] _ _ RNil true _ (() + τG)%ty);
        [apply CRefl_le|exact I|apply le.RExtend_le|apply le.TRefl_le|].
      apply Val_typed. apply InjL_val_typed. constructor. }
    1: { (* the call of the session with the main client and the leaks *)
      set (ρo := RCons (SFlip syntax.OS (SSig "out" (() + τG)%ty ()%ty)) RNil).
      eapply (App_typed _ [("scheduler", ((τG * (() + ())) ⇾ ())%ty); ("sys", TD)]
                [("sys", TD)] [] _ _ ρo RNil _ true _ ()%ty).
      6: { (* sys client *)
        assert (Hsys : <["out":=()]> ∅ .| [("sys", TD)] ⊢ₜ Var "sys" : RNil
                         : ((Acl ⇾ Bcl).|[ρo/])%ty ⊣ []).
        { eapply (RAbsElim_typed _ _ _ _ _ ρo (Acl ⇾ Bcl)%ty). apply Var_typed. }
        assert (Hfun : <["out":=()]> ∅ .| [("sys", TD)] ⊢ₜ Var "sys" : RNil
                         : (Acl.|[ρo/] -{ RNil }-∘ Bcl.|[ρo/])%ty ⊣ []).
        { eapply (Sub_typed _ _ [("sys", TD)] _ [] _ RNil false _ _);
            [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|exact Hsys]. }
        assert (Hc : <["out":=()]> ∅ .| [("sys", TD)] ⊢ₜ App (Var "sys") (main_client mz)
                       : RNil : Bcl.|[ρo/] ⊣ []).
        { eapply (App_typed _ [("sys", TD)] [("sys", TD)] [] _ _ RNil RNil RNil true
                    (Acl.|[ρo/]) (Bcl.|[ρo/]));
            [apply RRefl_le|apply RRefl_le|once_nil|apply RNil_le_ctx| |exact Hfun].
          apply main_client_typed. done. }
        pose proof (RAbsElim_typed _ _ _ _ _ RNil _ Hc) as H1.
        pose proof (RAbsElim_typed _ _ _ _ _ RNil _ H1) as H2.
        exact H2. }
      { apply le.RBot_le. }
      { asimpl. rewrite ?τG_cl ?τG_clt. apply row_call_nil. }
      { once_nil. }
      { constructor. }
      { apply typed_row_cons. asimpl. rewrite ?τG_cl.
        eapply Pair_typed; [once_nil| |].
        { eapply Pair_typed; [once_nil| |].
          { apply Val_typed. exact leak_send_typed. }
          { apply Val_typed. exact leak_recv_c_typed. } }
        { eapply Pair_typed; [once_nil| |].
          { apply Var_typed. }
          { apply Val_typed. exact leak_recv_k_typed. } } } }
  Qed.

  (* The scheduler as an environment of the security statement: it answers
     whether a message was delivered. *)
  Definition A_sched (mz : nat) : val :=
    (λ: "f", match: sched mz "f" with InjL <> => #false | InjR <> => #true end)%V.

  Lemma A_sched_typed (mz : nat) : ⊢ᵥ A_sched mz : ((() -∘ TD) ⇾ 𝔹)%ty.
  Proof using cg τG_cl τG_clt τG_nm.
    unfold A_sched.
    apply Rec_val_typed; first done. simpl.
    eapply (Match_typed _ [("f", (() -∘ TD)%ty)] [] [] _ _ _ _ _ RNil () τG 𝔹%ty);
      [solve_fresh|solve_fresh|solve_fresh|solve_fresh| | |].
    { eapply (App_typed _ [("f", (() -∘ TD)%ty)] [] [] _ _ RNil RNil RNil true
                (() -∘ TD)%ty (() + τG)%ty);
        [apply RRefl_le|apply RRefl_le|once_nil|apply RNil_le_ctx| |].
      { apply Var_typed. }
      { eapply (Sub_typed _ _ [] _ [] _ RNil false _ ((() -∘ TD) ⇾ (() + τG))%ty);
          [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|].
        apply Val_typed. apply sched_typed. } }
    { apply Val_typed. constructor. }
    { apply Val_typed. constructor. }
  Qed.

End sched_typed.

(* The scheduler in the security statement. *)

Section scheduler_correct.
  Local Open Scope R_scope.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.
  Context (τG_cl : ∀ σ : var → row, τG.|[σ] = τG).
  Context (τG_clt : ∀ σ : var → type, τG.[σ] = τG).
  Context (τG_nm : ∀ s : string, s ∉ vars._ty τG).

  (* The scheduler is an environment of the security statement for the
     composed system: the advantage of the scheduler, which tests for
     delivery, is bounded by the DDH advantage of the reduction. *)
  Corollary sched_advantage (mz : nat) :
    advantage (A_sched mz) REAL_DHKE_CHAN (SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN) #true <=
      advantage (RED_DHKE_CHAN (A_sched mz)) DH_real DH_rand #true.
  Proof using All. apply dhke_chan_realises_typed, A_sched_typed; done. Qed.

  (* Delivery and typing together: the scheduler is syntactically typed at
     the interface of [REAL_DHKE_CHAN], and run on [REAL_DHKE_CHAN] it
     terminates with probability one and returns the sent message. *)
  Theorem dhke_chan_delivers_typed (mz : nat) (m : vgG) (σ : state) :
    (∀ `{!probblazeRGS Σ}, vg_of_int_sem mz = Some m) →
    (⊢ᵥ sched mz : ((() -∘ T_DHKE_CHAN) ⇾ (() + τG))%ty) ∧
    lim_exec (sched mz REAL_DHKE_CHAN, σ) (SOMEV (vgval m)) = 1.
  Proof using All.
    intros Hmz. split; first apply sched_typed; try done.
    by apply dhke_chan_delivers.
  Qed.

End scheduler_correct.
