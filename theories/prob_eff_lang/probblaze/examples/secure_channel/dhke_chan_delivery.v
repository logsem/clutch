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
   program: with probability one it terminates and returns the message. *)

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

  (* The honest answers to the leaks. *)
  Definition leak_send : val := (λ: "x", #()%V)%V.
  Definition leak_recv : val := (λ: "x", SOME #0)%V.
  Definition honest_leaks : val := ((leak_send, leak_recv), (leak_send, leak_recv))%V.

  (* The nested client activates Bob: it receives once. *)
  Definition nested_client : val :=
    (λ: "ops", let, ("ssend", "srecv") := "ops" in "srecv" #()%V ;; #()%V)%V.

  (* One session [sys]; the leak of Alice's message re-enters it with the
     nested client and honest leaks; the main client sends [mz], then receives
     and records what it got. *)
  Definition sched_prog (mz : Z) : expr :=
    let: "sys" := REAL_DHKE_CHAN #()%V in
    let: "res" := ref NONEV in
    let: "scheduler" := (λ: "x", "sys" nested_client honest_leaks) in
    "sys" (λ: "ops", let, ("ssend", "srecv") := "ops" in
                     "ssend" #mz ;; "res" <- ("srecv" #()%V))
          ((leak_send, leak_recv), ("scheduler", leak_recv)) ;;
    !"res".

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
    rewrite /sched_prog /REAL_DHKE_CHAN /nested_client /honest_leaks /leak_send /leak_recv.
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
    brel_alloc_r res as "Hres". brel_pures_r.
    brel_effect_r l_as as "Hl_as". try (try brel_pures_r).
    brel_effect_r l_ar as "Hl_ar". try (try brel_pures_r).
    brel_effect_r l_gk as "Hl_gk". try (try brel_pures_r).
    brel_effect_r l_os as "Hl_os". try (try brel_pures_r).
    brel_effect_r l_or as "Hl_or". try (try brel_pures_r).
    brel_effect_r l_ss as "Hl_ss". try (try brel_pures_r).
    brel_effect_r l_sr as "Hl_sr". try (try brel_pures_r).
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
    brel_store_r. pr.
    brel_load_r. pr.
    rewrite (expgAC g a b) (mask_involutive _ m).
    iApply brel_value. iIntros "Hna". iModIntro. iFrame. done.
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
