From clutch.elton Require Import elton.
From clutch.elton.lib Require Import map.

Set Default Proof Using "Type*".

Section simple_bit_hash.

  Context `{!eltonGS Σ}.

  Variable val_size : nat.

  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
  Definition compute_hash_specialized hm : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand #val_size) in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand #val_size) in
          set "hm" "v" "b";;
          "b"
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      compute_hash "hm".

  (* (* A hash function is collision free if the partial map it *)
  (*    implements is an injective function *) *)
  (* Definition coll_free (m : gmap nat nat) := *)
  (*   forall k1 k2, *)
  (*   is_Some (m !! k1) -> *)
  (*   is_Some (m !! k2) -> *)
  (*   m !!! k1 = m !!! k2 -> *)
  (*   k1 = k2. *)

  (* Definition hashfun f m : iProp Σ := *)
  (*   ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ *)
  (*                 map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗ *)
  (*                 ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝ *)
  (* . *)

  (* Definition coll_free_hashfun f m: iProp Σ := *)
  (*   hashfun f m ∗ ⌜coll_free m⌝. *)

  (* Lemma coll_free_hashfun_implies_hashfun f m: *)
  (*   coll_free_hashfun f m -∗ hashfun f m. *)
  (* Proof. *)
  (*   by iIntros "[??]". *)
  (* Qed. *)

  (* #[global] Instance timeless_hashfun f m : *)
  (*   Timeless (hashfun f m). *)
  (* Proof. apply _. Qed. *)

  (* #[global] Instance timeless_hashfun_amortized f m: *)
  (*   Timeless (coll_free_hashfun f m). *)
  (* Proof. apply _. Qed. *)

  (* Lemma coll_free_hashfun_implies_coll_free f m: *)
  (*   coll_free_hashfun f m -∗ ⌜coll_free m⌝. *)
  (* Proof. *)
  (*   by iIntros "[??]". *)
  (* Qed. *)

  (* Lemma hashfun_implies_bounded_range f m idx x: *)
  (*   hashfun f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝. *)
  (* Proof. *)
  (*   iIntros "(%&%&H&%K) %". *)
  (*   iPureIntro. *)
  (*   by eapply map_Forall_lookup_1 in K. *)
  (* Qed. *)

  (* Lemma coll_free_hashfun_implies_bounded_range f m idx x: *)
  (*   coll_free_hashfun f m -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝. *)
  (* Proof. *)
  (*   iIntros "(H&%) %". *)
  (*   by iApply (hashfun_implies_bounded_range with "[$]"). *)
  (* Qed. *)

  (* Lemma wp_init_hash E : *)
  (*   {{{ True }}} *)
  (*     init_hash #() @ E *)
  (*   {{{ f, RET f; |={E}=> coll_free_hashfun f ∅ }}}. *)
  (* Proof. *)
  (*   rewrite /init_hash. *)
  (*   iIntros (Φ) "_ HΦ". *)
  (*   wp_pures. rewrite /init_hash_state. *)
  (*   wp_apply (wp_init_map with "[//]"). *)
  (*   iIntros (?) "Hm". wp_pures. *)
  (*   rewrite /compute_hash. wp_pures. *)
  (*   iApply "HΦ". repeat iModIntro. rewrite /coll_free_hashfun. iSplit. *)
  (*   - iExists _. rewrite fmap_empty. iFrame. eauto. *)
  (*   - iPureIntro. rewrite /coll_free. intros ???H?. destruct H. *)
  (*     by apply lookup_empty_Some in H. *)
  (* Qed. *)

  (* Lemma coll_free_insert (m : gmap nat nat) (n : nat) (z : nat) : *)
  (*   m !! n = None -> *)
  (*   coll_free m -> *)
  (*   Forall (λ x, z ≠ snd x) (map_to_list m) -> *)
  (*   coll_free (<[ n := z ]>m). *)
  (* Proof. *)
  (*   intros Hnone Hcoll HForall. *)
  (*   intros k1 k2 Hk1 Hk2 Heq. *)
  (*   apply lookup_insert_is_Some' in Hk1. *)
  (*   apply lookup_insert_is_Some' in Hk2. *)
  (*   destruct (decide (n = k1)). *)
  (*   - destruct (decide (n = k2)); simplify_eq; auto. *)
  (*     destruct Hk2 as [|Hk2]; auto. *)
  (*     rewrite lookup_total_insert in Heq. *)
  (*     rewrite lookup_total_insert_ne // in Heq. *)
  (*     apply lookup_lookup_total in Hk2. *)
  (*     rewrite -Heq in Hk2. *)
  (*     eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first. *)
  (*     { intros (?&?); eauto. } *)
  (*     eapply map_Forall_to_list in HForall. *)
  (*     rewrite /map_Forall in HForall. *)
  (*     eapply HForall in Hk2; congruence. *)
  (*   - destruct (decide (n = k2)); simplify_eq; auto. *)
  (*     { *)
  (*       destruct Hk1 as [|Hk1]; auto. *)
  (*       rewrite lookup_total_insert in Heq. *)
  (*       rewrite lookup_total_insert_ne // in Heq. *)
  (*       apply lookup_lookup_total in Hk1. *)
  (*       rewrite Heq in Hk1. *)
  (*       eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first. *)
  (*       { intros (?&?); eauto. } *)
  (*       eapply map_Forall_to_list in HForall. *)
  (*       rewrite /map_Forall in HForall. *)
  (*       eapply HForall in Hk1; congruence. *)
  (*     } *)
  (*     rewrite ?lookup_total_insert_ne // in Heq. *)
  (*     destruct Hk1 as [|Hk1]; try congruence; []. *)
  (*     destruct Hk2 as [|Hk2]; try congruence; []. *)
  (*     apply Hcoll; eauto. *)
  (* Qed. *)


  (* Lemma wp_hashfun_prev E f m (n : nat) (b : nat) : *)
  (*   m !! n = Some b → *)
  (*   {{{ hashfun f m }}} *)
  (*     f #n @ E *)
  (*   {{{ RET #b; hashfun f m }}}. *)
  (* Proof. *)
  (*   iIntros (Hlookup Φ) "Hhash HΦ". *)
  (*   iDestruct "Hhash" as (hm ->) "[H Hbound]". *)
  (*   rewrite /compute_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]"). *)
  (*   iIntros (vret) "(Hhash&->)". *)
  (*   rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ". *)
  (*   iExists _. eauto. *)
  (* Qed. *)

  (* Lemma wp_coll_free_hashfun_prev E f m (n : nat) (b : nat) : *)
  (*   m !! n = Some b → *)
  (*   {{{ coll_free_hashfun f m }}} *)
  (*     f #n @ E *)
  (*   {{{ RET #b; coll_free_hashfun f m }}}. *)
  (* Proof. *)
  (*   iIntros (Hlookup Φ) "(Hhash & %Hcoll_free) HΦ". *)
  (*   iDestruct "Hhash" as (hm ->) "[H Hbound]". *)
  (*   rewrite /compute_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]"). *)
  (*   iIntros (vret) "(Hhash&->)". *)
  (*   rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ". *)
  (*   iSplitL; last done. *)
  (*   iExists _. eauto. *)
  (* Qed. *)


  (* Lemma wp_insert_no_coll E f m (n : nat) : *)
  (*   m !! n = None → *)
  (*   {{{ coll_free_hashfun f m ∗ ↯ (nnreal_div (nnreal_nat (length (map_to_list m))) (nnreal_nat(val_size+1))) *)
  (*   }}} *)
  (*     f #n @ E *)
  (*   {{{ (v : nat), RET #v; coll_free_hashfun f (<[ n := v ]>m) }}}. *)
  (* Proof. *)
  (*   iIntros (Hlookup Φ) "([Hhash %Hcoll_free] & Herr) HΦ". *)
  (*   iDestruct "Hhash" as (hm ->) "[H %Hbound]". *)
  (*   rewrite /compute_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]"). *)
  (*   iIntros (vret) "(Hhash&->)". *)
  (*   rewrite lookup_fmap Hlookup /=. wp_pures. *)
  (*   wp_bind (rand _)%E. *)
  (*   wp_apply (wp_rand_err_list_nat _ val_size (map (λ p, snd p) (map_to_list m))); auto. *)
  (*   rewrite length_map. *)
  (*   rewrite plus_INR INR_1. *)
  (*   iFrame. *)
  (*   iIntros "%x [%Hx %HForall]". *)
  (*   wp_pures. *)
  (*   wp_apply (wp_set with "Hhash"). *)
  (*   iIntros "Hlist". *)
  (*   wp_pures. *)
  (*   iModIntro. *)
  (*   iApply "HΦ". *)
  (*   iSplit. *)
  (*   - rewrite /hashfun. *)
  (*     iExists _. *)
  (*     iSplit; first auto. *)
  (*     iSplitL. *)
  (*     + rewrite fmap_insert //. *)
  (*     + iPureIntro. *)
  (*       apply map_Forall_insert_2; last done. *)
  (*       split; lia. *)
  (*   - iPureIntro. *)
  (*     apply coll_free_insert; auto. *)
  (*     apply (Forall_map (λ p : nat * nat, p.2)) in HForall; auto. *)
  (* Qed. *)


End simple_bit_hash.
