From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import dhke_common.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_handlers.

(** * The DHKE cores' building blocks, in both directions

    The protocol [DH_KE] (and [DH_SIM]) is the program [l]: its state is
    described with [↦ₗ] and [↪ₗ], the reduction's with [↦ᵣ]. *)

Section dhke_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.
  Import valgroup_notation.

  (* Alice's [sample_or_read] in [l]: the first call reads the exponent [a]
     from the tape; the reduction stores the key [g^c] on its first call. *)
  Lemma eq_sample_or_read_store E α (s : string) (a c : nat) la lcs K K' X R :
    ⊢ (α ↪ₗN (n; [a]) ∗ la ↦ₗ InjLV #()%V ∗ lcs ↦ᵣ InjLV #()%V ∨
       α ↪ₗ□N (n; []) ∗ la ↦ₗ□ InjRV #a ∗ lcs ↦ᵣ□ InjRV (vgval (g ^+ c))) -∗
      (la ↦ₗ□ InjRV #a -∗ α ↪ₗ□N (n; []) -∗ lcs ↦ᵣ□ InjRV (vgval (g ^+ c)) -∗
         EQ fill K #a ≈ fill K' #()%V @ E <|X|> {{ R }}) -∗
      EQ fill K (match: ! #la with InjL <> => let: s := #()%V;; rand(#lbl:α) #n in #la <- InjR s;; s | InjR s => s end)
       ≈ fill K' (match: ! #lcs with InjL <> => #lcs <- InjR (vgval (g ^+ c)) | InjR "key" => #()%V end)
        @ E <|X|> {{ R }}.
  Proof.
    iIntros "[(Hα & Hla & Hlcs) | (#Hα & #Hla & #Hlcs)] Hk".
    - eq_load_l. rewrite fill_app /=. eq_pures_l.
      eq_rand_l as "%Ha". rewrite fill_app /=. eq_pures_l. rewrite decide_True //. eq_pures_l.
      eq_store_l. rewrite fill_app /=. eq_pures_l.
      eq_load_r. rewrite fill_app /=. eq_pures_r. eq_store_r.
      iMod (eq_pt_l_persist with "Hla") as "#Hla".
      iMod (eq_tp_l_persist with "Hα") as "#Hα".
      iMod (eq_pt_r_persist with "Hlcs") as "#Hlcs".
      by iApply "Hk".
    - eq_load_l. rewrite fill_app /=. eq_pures_l. rewrite decide_True //.
      eq_load_r. rewrite fill_app /=. eq_pures_r.
      by iApply "Hk".
  Qed.

  (* Bob's [sample_or_read] in [l]. *)
  Lemma eq_sample_or_read E β (s : string) (b : nat) lb K er X R :
    ⊢ (β ↪ₗN (n; [b]) ∗ lb ↦ₗ InjLV #()%V ∨ β ↪ₗ□N (n; []) ∗ lb ↦ₗ□ InjRV #b) -∗
      (lb ↦ₗ□ InjRV #b -∗ β ↪ₗ□N (n; []) -∗ EQ fill K #b ≈ er @ E <|X|> {{ R }}) -∗
      EQ fill K (match: ! #lb with InjL <> => let: s := #()%V;; rand(#lbl:β) #n in #lb <- InjR s;; s | InjR s => s end)
       ≈ er @ E <|X|> {{ R }}.
  Proof.
    iIntros "[(Hβ & Hlb) | (#Hβ & #Hlb)] Hk".
    - eq_load_l. rewrite fill_app /=. eq_pures_l.
      eq_rand_l as "%Hb". rewrite fill_app /=. eq_pures_l. rewrite decide_True //. eq_pures_l.
      eq_store_l. rewrite fill_app /=. eq_pures_l.
      iMod (eq_pt_l_persist with "Hlb") as "#Hlb".
      iMod (eq_tp_l_persist with "Hβ") as "#Hβ".
      by iApply "Hk".
    - eq_load_l. rewrite fill_app /=. eq_pures_l. rewrite decide_True //.
      by iApply "Hk".
  Qed.

  (** The authenticated channel, with predicates [Pa] on Alice's messages
      and [Pb] on Bob's, which may depend on the direction. *)
  Definition eq_chan_thy (Pa Pb : vgG → iPropD Σ) γtoka γtokb γfraca γfracb (sl sr rl rr : label) :
      dir → iLblThy Σ :=
    λ d, iLblSig_to_iLblThy (chan_new_row (λ m, Pa m d) (λ m, Pb m d) γtoka atokN γtokb btokN γfraca γfracb
                               (pick d sl sr) (pick d sr sl) (pick d rl rr) (pick d rr rl)).

  Section chan.
    Context (Pa Pb : vgG → iPropD Σ) (γtoka γtokb γfraca γfracb : gname) (sl sr rl rr : label).
    Context (X : eqThy Σ).
    Context (Hsub : ∀ d, eq_chan_thy Pa Pb γtoka γtokb γfraca γfracb sl sr rl rr d ⊆ eq_thy_at X d).

    (* Alice sends [m] to Bob. *)
    Lemma eq_chan_send_bob kl kr (m : vgG) R :
      NeutralEctx [sl] kl → NeutralEctx [sr] kr →
      ⊢ □ Pa m -∗ ⎡inv atokN (token γtoka ∨ receipt γfraca)⎤ -∗
        EQ fill kl #()%V ≈ fill kr #()%V <|X|> {{ R }} -∗
        EQ fill kl (do: sl (vgval m, bob)%V) ≈ fill kr (do: sr (vgval m, bob)%V) <|X|> {{ R }}.
    Proof using Hsub.
      intros Hkl Hkr. iStartProof (iProp _). iIntros (d) "#HP #Hinv Hk". rewrite !eq_rel_at.
      destruct d; rewrite /pick /=;
        (iApply brel_introduction'; [apply Hsub; rewrite /eq_chan_thy /pick /=; by apply list_elem_of_further, list_elem_of_here|]);
        iExists _, _, _, _, _; (do 4 (iSplit; [done|])); (iSplitL; [|by iIntros "!>" (??) "H"]);
        iLeft; iExists m, m; (iSplitR; [iApply send_upd; by iFrame "#"|]); (iSplit; [done|]); iFrame.
    Qed.

    (* Bob sends [m] to Alice. *)
    Lemma eq_chan_send_alice kl kr (m : vgG) R :
      NeutralEctx [sl] kl → NeutralEctx [sr] kr →
      ⊢ □ Pb m -∗ ⎡inv btokN (token γtokb ∨ receipt γfracb)⎤ -∗
        EQ fill kl #()%V ≈ fill kr #()%V <|X|> {{ R }} -∗
        EQ fill kl (do: sl (vgval m, alice)%V) ≈ fill kr (do: sr (vgval m, alice)%V) <|X|> {{ R }}.
    Proof using Hsub.
      intros Hkl Hkr. iStartProof (iProp _). iIntros (d) "#HP #Hinv Hk". rewrite !eq_rel_at.
      destruct d; rewrite /pick /=;
        (iApply brel_introduction'; [apply Hsub; rewrite /eq_chan_thy /pick /=; by apply list_elem_of_further, list_elem_of_here|]);
        iExists _, _, _, _, _; (do 4 (iSplit; [done|])); (iSplitL; [|by iIntros "!>" (??) "H"]);
        iRight; iExists m, m; (iSplitR; [iApply send_upd; by iFrame "#"|]); (iSplit; [done|]); iFrame.
    Qed.

    (* Receiving Alice's message, if she has sent one. *)
    Lemma eq_chan_recv_alice kl kr R :
      NeutralEctx [rl] kl → NeutralEctx [rr] kr →
      ⊢ (EQ fill kl NONEV ≈ fill kr NONEV <|X|> {{ R }} ∧
         ∀ m : vgG, Pa m -∗ EQ fill kl (SOMEV (vgval m)) ≈ fill kr (SOMEV (vgval m)) <|X|> {{ R }}) -∗
        EQ fill kl (do: rl alice) ≈ fill kr (do: rr alice) <|X|> {{ R }}.
    Proof using Hsub.
      intros Hkl Hkr. iStartProof (iProp _). iIntros (d) "Hk". rewrite !eq_rel_at.
      destruct d; rewrite /pick /=;
        (iApply brel_introduction'; [apply Hsub; rewrite /eq_chan_thy /pick /=; by apply list_elem_of_here|]);
        iExists _, _, _, _, _; (do 4 (iSplit; [done|])); (iSplitL; [|by iIntros "!>" (??) "H"]);
        iLeft; (do 2 (iSplit; [done|])); (iSplit; [by iDestruct "Hk" as "[H _]"|]);
        iIntros (m) "HP"; iDestruct "Hk" as "[_ H]"; iSpecialize ("H" $! m with "HP"); by rewrite eq_rel_at /pick /=.
    Qed.

    (* Receiving Bob's message, if he has sent one. *)
    Lemma eq_chan_recv_bob kl kr R :
      NeutralEctx [rl] kl → NeutralEctx [rr] kr →
      ⊢ (EQ fill kl NONEV ≈ fill kr NONEV <|X|> {{ R }} ∧
         ∀ m : vgG, Pb m -∗ EQ fill kl (SOMEV (vgval m)) ≈ fill kr (SOMEV (vgval m)) <|X|> {{ R }}) -∗
        EQ fill kl (do: rl bob) ≈ fill kr (do: rr bob) <|X|> {{ R }}.
    Proof using Hsub.
      intros Hkl Hkr. iStartProof (iProp _). iIntros (d) "Hk". rewrite !eq_rel_at.
      destruct d; rewrite /pick /=;
        (iApply brel_introduction'; [apply Hsub; rewrite /eq_chan_thy /pick /=; by apply list_elem_of_here|]);
        iExists _, _, _, _, _; (do 4 (iSplit; [done|])); (iSplitL; [|by iIntros "!>" (??) "H"]);
        iRight; (do 2 (iSplit; [done|])); (iSplit; [by iDestruct "Hk" as "[H _]"|]);
        iIntros (m) "HP"; iDestruct "Hk" as "[_ H]"; iSpecialize ("H" $! m with "HP"); by rewrite eq_rel_at /pick /=.
    Qed.
  End chan.

  (** The client's key queries *)

  (* The key-query operation is well typed against a row with the theory
     [GetKey gl gr]: [θ gl gr], or the same with the leak labels of the
     simulator on one side. *)
  Local Ltac gk_typed_tac :=
    rewrite /sem_ty_arr /sem_ty_mbang /=;
    iIntros "!>" (??) "#(%&%&[(->&->&->&->)|(->&->&->&->)])";
      brel_pures'; (iApply brel_introduction'; [by apply list_elem_of_here|]);
      (iExists _,_,[],[],_; do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
      iSplit; try (iIntros (??) "!# H"; iApply "H");
      iSplit; first (iPureIntro; (left + right); split; done);
      iModIntro; iSplitL; last iIntros (key); brel_pures'; iApply brel_value; iIntros "$ !>";
      iExists _,_; [iLeft; by iPureIntro | iRight; iPureIntro; repeat (split; first done); by eexists]).

  Lemma gk_typed (gl gr : label) :
    ⊢ ((𝟙 + 𝟙)%T -{ θ gl gr }-> (Option 𝔾))%T (λ: "party", do: gl "party")%V (λ: "party", do: gr "party")%V.
  Proof. gk_typed_tac. Qed.

  Lemma gkleakl_typed (ls lr gl gr : label) :
    ⊢ ((𝟙 + 𝟙)%T -{ gkleakl ls lr gl gr }-> (Option 𝔾))%T (λ: "party", do: gl "party")%V (λ: "party", do: gr "party")%V.
  Proof. gk_typed_tac. Qed.

  Lemma gkleakr_typed (ls lr gl gr : label) :
    ⊢ ((𝟙 + 𝟙)%T -{ gkleakr ls lr gl gr }-> (Option 𝔾))%T (λ: "party", do: gl "party")%V (λ: "party", do: gr "party")%V.
  Proof. gk_typed_tac. Qed.

  (* The client's row in the simulated world: the simulator's leak labels
     [ls], [lr] go with the key-query label [gl] of [l]. *)
  Definition gkleak_row (ls lr gl gr : label) (d : dir) : sem_row Σ :=
    match d with Fwd => gkleakl ls lr gl gr | Bwd => gkleakr ls lr gr gl end.

  (* The theory of the client's queries, as the row [¡ θ gl gr] gives it. *)
  Definition gk_thy (gl gr : label) : dir → iThy Σ :=
    λ d, iThyMono (GetKey (pick d gl gr) (pick d gr gl)).

  Lemma gk_thy_app gl gr el er (Q : expr -d> expr -d> iProp Σ) :
    eq_thy_app (gk_thy gl gr) el er Q ⊢
      ∃ Q' : expr -d> expr -d> iProp Σ,
        ⌜(el = (do: gl (InjLV #()%V))%E ∧ er = (do: gr (InjLV #()%V))%E) ∨
         (el = (do: gl (InjRV #()%V))%E ∧ er = (do: gr (InjRV #()%V))%E)⌝ ∗
        □ (⎡Q' NONEV NONEV⎤ ∗ ∀ key : vgG, ⎡Q' (SOMEV (vgval key)) (SOMEV (vgval key))⎤) ∗
        ▷ (∀ sl sr, ⎡Q' sl sr⎤ -∗ ⎡Q sl sr⎤).
  Proof.
    iStartProof (iProp _). iIntros (d) "H". rewrite /eq_thy_app /gk_thy /=.
    destruct d; rewrite /pick /=; iDestruct "H" as (Q') "(([[-> ->]|[-> ->]] & #[Hn Hs]) & HQ)".
    1,2: iExists Q'; iSplit; [iPureIntro; by [left|right]|]; iSplit; [iIntros "!>"; iSplitR; [iApply "Hn"|iIntros (k); iApply "Hs"]|];
      iIntros "!>" (sl sr) "H"; by iApply "HQ".
    all: iExists (λ s1 s2, Q' s2 s1); iSplit; [iPureIntro; by [left|right]|]; iSplit; [iIntros "!>"; iSplitR; [iApply "Hn"|iIntros (k); iApply "Hs"]|];
      iIntros "!>" (sl sr) "H"; by iApply "HQ".
  Qed.

End dhke_eq.
