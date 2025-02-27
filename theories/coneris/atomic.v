From stdpp Require Import namespaces.
From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic.
From iris.proofmode Require Import proofmode classes.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
From coneris.coneris Require Import coneris.

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else.

For the non-atomic post-condition, we use an [option PROP], combined with a
[-∗?]. This is to avoid introducing spurious [True -∗] into proofs that do not
need a non-atomic post-condition (which is most of them). *)
Definition atomic_wp `{!conerisGS Σ} {TA TB TP : tele}
  (e: expr) (* expression *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (POST: TA → TB → TP → option (iProp Σ)) (* non-atomic post-condition *)
  (f: TA → TB → TP → val) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : val → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_update (⊤∖E) ∅ α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
            WP e {{ Φ }}.

(** We avoid '<<{'/'}>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ Some POST%I
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ v%V
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app $ Some POST%I)
             (tele_app $ tele_app $ tele_app $ v%V)
  )
  (at level 20, E, β, α, v, POST at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app None) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app None)
             (tele_app $ tele_app $ tele_app v%V)
  )
  (at level 20, E, β, α, v at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
    : bi_scope.

(** Theory *)
Section lemmas.
  Context `{!conerisGS Σ} {TA TB TP : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → val).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_wp_seq e E α β POST f :
    atomic_wp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply (pgl_wp_frame_wand with "HΦ"). iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. iIntros (z) "Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e E α β POST f :
    TCEq (to_val e) None →
    atomic_wp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }}.
  Proof.
    iIntros (?) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (pgl_wp_step_fupd _ _ ⊤ _ (∀.. y : TB, _)
      with "[$HΦ //]"); first done.
    iApply (atomic_wp_seq with "H Hα").
    iIntros "%y Hβ %z Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_wp_atomic e E α β POST f `{!Atomic StronglyAtomic e} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ ∅ {{ Φ }}) -∗
    atomic_wp e E α β POST f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros "%y Hβ %z Hpost".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_wp_atomic e E (α : [tele] → iProp) (β : [tele] → TB → iProp)
      (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → val)
      {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ WP e {{ Φ }}) -∗
    atomic_wp e E α β POST f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_pgl_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply pgl_wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!> %y Hβ %z Hpost".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  Lemma atomic_wp_mask_weaken e E1 E2 α β POST f :
    E1 ⊆ E2 → atomic_wp e E1 α β POST f -∗ atomic_wp e E2 α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_wp_inv e E α β POST f N I :
    ↑N ⊆ E →
    atomic_wp e (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_wp e E α β POST f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.

