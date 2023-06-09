From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

Definition xor b1 b2 : expr :=
  let not b := (if: b then #false else #true)%E in
  if: b1 then not b2 else b2.
Definition xor_sem (b1 b2 : bool) :=
  if b1 then negb b2 else b2.

Ltac foldxor := assert (forall b2, (if: _ then (if: b2 then #false else #true) else b2)%E = (xor _ _)) as -> by easy.

(* The ideal encryption scheme returns a random bit. Can't get more uninformative than that.  *)
Definition ideal : expr := λ:"msg", flip.
(* The real one-time pad generates a random key the size of the message and returns the xor. *)
Definition real : expr := λ:"msg", let: "k" := flip in xor "msg" "k".
(* We want to show that "real" looks random, i.e. is indistinguishable from "ideal". *)

Section logical_ref.
  Context `{!clutchRGS Σ}.

  Global Instance xor_invol_1 : forall b, Involutive eq (xor_sem b) | 2.
  Proof. intros [] [] => //. Qed.

  Global Instance xor_inj_1 : forall b, Inj (=) (=) (xor_sem b) | 2.
  Proof. intros. apply cancel_inj. Qed.

  Global Instance xor_surj_1 : forall b, Surj (=) (xor_sem b) | 2.
  Proof. intros. apply cancel_surj. Qed.

  Global Instance xor_bij_1 : forall b, Bij (xor_sem b) | 2.
  Proof. constructor ; apply _. Qed.

  Global Instance xor_comm : Comm (=) xor_sem | 2.
  Proof. intros [] [] => //. Qed.

  Lemma xor_tp E (b1 b2 : bool) :
    ↑specN ⊆ E → ⊢ ∀ K, refines_right K (xor #b1 #b2) ={E}=∗ refines_right K (#(xor_sem b1 b2)).
  Proof.
    destruct b1, b2 ; iIntros ; tp_pures ; iModIntro ; done.
  Qed.

  Lemma xor_wp (b1 b2 : bool) :
    ⊢ WP xor #b1 #b2 {{v, ⌜v = #(xor_sem b1 b2)⌝}}.
  Proof.
    rewrite /xor /xor_sem /negb. destruct b1, b2 ; wp_pures ; done.
  Qed.

  Lemma xor_xor_sem (b1 b2 : bool) :
    ⊢ REL xor #b1 #b2 << #(xor_sem b1 b2) : lrel_bool.
  Proof.
    rewrite /xor /xor_sem /negb. destruct b1, b2 ; rel_pures_l ; rel_values ; done.
  Qed.

  (* We should a bi-refinement, carefully choosing the relation of the sampled bits. *)
  Lemma real_ideal_rel :
    ⊢ REL real << ideal : lrel_bool → lrel_bool.
  Proof with foldxor.
    rewrite /real /ideal.
    rel_arrow_val.
    iIntros (msg1 msg2) "Hmsg".
    rel_pures_l. rel_pures_r.
    foldxor.
    iDestruct "Hmsg" as "[%b_msg [-> ->]]".
    rel_apply (refines_couple_flip_flip (xor_sem b_msg)).
    simpl.
    iIntros "!>" (k).
    rel_pures_l...
    iApply xor_xor_sem.
  Qed.

  Lemma ideal_real_rel :
    ⊢ REL ideal << real : lrel_bool → lrel_bool.
  Proof.
    rewrite /real /ideal.
    rel_arrow_val.
    iIntros (msg1 msg2) "Hmsg".
    rel_pures_l. rel_pures_r.
    iDestruct "Hmsg" as "[%msg [-> ->]]".
    rel_apply (refines_couple_flip_flip (xor_sem msg)) => /=.
    iIntros "!>" (k).
    rel_pures_r.
    foldxor.
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|].
    rewrite cancel.
    rel_values.
  Qed.

  (* We prove that the OTP has "one-time uniform ciphertexts". *)
  Definition L_ots_rand_real (size keygen enc : expr) : expr :=
    λ: "m" ,
      let: "k" := keygen #() in
      enc "k" "m".

  Definition sampler : expr :=
    rec: "f" "n" :=
      if: "n" < #1 then
        #()
      else
        let: "b" := flip in
        ("b", "f" ("n" - #1)).

  Definition L_ots_rand_rand (size keygen enc : expr) : expr :=
    λ: "_" ,
      sampler size.

  Definition keygen := (λ:<>, flip)%E.
  Definition enc := (λ:"k" "m", (xor "k" "m", #()))%E.
  Definition size := 1.

  Fixpoint lrel_bitlist n : lrel Σ :=
    match n with
    | O => lrel_unit
    | S n' => lrel_prod lrel_bool (lrel_bitlist n')
    end.

  Lemma L_ots_rr :
    ⊢ REL L_ots_rand_real #size keygen enc
      << L_ots_rand_rand #size keygen enc
      : lrel_bool → lrel_bitlist size.
  Proof.
    unfold L_ots_rand_rand, L_ots_rand_real, enc, keygen.
    rel_arrow_val.
    iIntros (msg1 msg2) "[%msg [-> ->]]" ;
      rel_pures_l ; rel_pures_r.
    rel_apply (refines_couple_flip_flip (xor_sem msg)) => /=.
    iIntros "!>" (k).
    rel_pures_l.
    foldxor.
    do 6 rel_pure_r.
    iApply refines_pair.
    2: rel_values.
    rewrite /xor /xor_sem /negb.
    destruct k, msg ; rel_pures_l ; rel_values ; done.
  Qed.

  Lemma L_ots_rr' :
    ⊢ REL L_ots_rand_rand #size keygen enc
      << L_ots_rand_real #size keygen enc
      : lrel_bool → lrel_bitlist size.
  Proof.
    unfold L_ots_rand_rand, L_ots_rand_real, enc, keygen.
    rel_arrow_val.
    iIntros (msg1 msg2) "[%msg [-> ->]]" ;
      rel_pures_l ; rel_pures_r.
    rel_apply (refines_couple_flip_flip (xor_sem msg)) => /=.
    iIntros "!>" (k).
    do 6 rel_pure_l.
    rel_pures_r.
    foldxor.
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|].
    iModIntro.
    iApply refines_pair.
    2: rel_values.
    rewrite comm.
    rewrite cancel.
    rel_values.
  Qed.

End logical_ref.
