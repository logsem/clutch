From clutch.coneris Require Import coneris .

Set Default Proof Using "Type*".

(** This spec is not strong enough to say anything about how the value hashed must be somthing we presampled
    For that info, please refer to interface1
*)

Class con_hash0 `{!conerisGS Σ} (val_size:nat):= Con_Hash0
{
  (** * Operations *)
  init_hash0 : val;
  (* incr_counter : val; *)
  allocate_tape0 : val;
  compute_hash0 : val;
  (** * Ghost state *)
  
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  
  hash_view_gname:Type;
  hash_lock_gname:Type;
  
  (** * Predicates *)
  con_hash_inv0 (N:namespace) (f l hm: val) (γ1:hash_view_gname)(γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape0 (α:val) (ns:list nat) : iProp Σ;
  hash_auth0 (m:gmap nat nat) (γ2:hash_view_gname) : iProp Σ;
  hash_frag0 (v res:nat) (γ:hash_view_gname): iProp Σ;
  
  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_tape_timeless α ns ::
    Timeless (hash_tape0 α ns); 
  #[global] hash_map_timeless m γ ::
    Timeless (hash_auth0 m γ);
  #[global] hash_frag_timeless v res γ ::
    Timeless (hash_frag0 v res γ);
  #[global] con_hash_inv_persistent N f l hm γ1 γ_lock ::
    Persistent (con_hash_inv0 N f l hm γ1 γ_lock);
  #[global] hash_frag_persistent v res γ ::
    Persistent (hash_frag0 v res γ);
  
  hash_tape_valid α ns:
    hash_tape0 α ns -∗ ⌜Forall (λ x, x<=val_size)%nat ns⌝;
  hash_auth_exclusive m m' γ:
    hash_auth0 m γ -∗ hash_auth0 m' γ -∗ False;
  hash_auth_frag_agree m k v γ:
    hash_auth0 m γ -∗ hash_frag0 k v γ -∗ ⌜m!!k = Some v⌝;
  hash_frag_frag_agree k v1 v2 γ :
    hash_frag0 k v1 γ -∗ hash_frag0 k v2 γ -∗ ⌜v1=v2⌝;
  hash_auth_duplicate_frag m k v γ:
    m!!k=Some v -> hash_auth0 m γ -∗ hash_frag0 k v γ;
  hash_auth_insert m k v γ:
    m!!k=None -> hash_auth0 m γ ==∗ (hash_auth0 (<[k:=v]> m) γ ∗ hash_frag0 k v γ);
                      

  con_hash_presample0 E (ε:nonnegreal) ns α (ε2 : fin (S val_size) → R) :
    (∀ x : fin (S val_size), (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    hash_tape0 α ns -∗
    ↯ ε -∗
    state_update E E (∃ n,
          ↯ (ε2 n) ∗
          hash_tape0 α (ns++[fin_to_nat n]) 
      );

  con_hash_init0 N:
    {{{ True }}}
      init_hash0 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ_lock, con_hash_inv0 N f l hm γ1 γ_lock }}};

  con_hash_alloc_tape0:
    {{{ True }}}
      allocate_tape0 #()
      {{{ (α: val), RET α; hash_tape0 α [] }}};
  
  con_hash_spec0 N f l hm γ1 γlock α ns (v:nat) P Q:
  {{{ con_hash_inv0 N f l hm γ1 γlock ∗ hash_tape0 α (ns) ∗
      ( ∀ m, hash_auth0 m γ1 ={⊤∖↑N}=∗
             match m!!v with
             | Some res => hash_auth0 m γ1 ∗ P res
             | None => ∃ n ns', ⌜n::ns'=ns⌝ ∗ hash_auth0 (<[v:=n]> m) γ1 ∗ Q
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (hash_tape0 α (ns) ∗ P res ∨
                                 ∃ n ns', ⌜n::ns'=ns⌝ ∗ hash_tape0 α ns' ∗ ⌜res=n⌝ ∗ Q 
                                )
      }}};
  (* con_hash_spec_hashed_before0 f l hm γ1 γ2 γlock α ns res (v:nat): *)
  (*   {{{ con_hash_inv0 f l hm γ1 γ2 γlock ∗ hash_tape0 α ns ∗ hash_frag0 v res γ1}}} *)
  (*     f #v α *)
  (*     {{{ RET (#res);  hash_frag0 v res γ1 ∗ *)
  (*                      (hash_tape0 α ns) *)
  (*     }}} *)
}.

Section test.
  Context `{conerisGS Σ, !con_hash0 val_size}.
  Lemma con_hash_spec0' N f l hm γ1 γlock α n ns (v:nat):
    {{{ con_hash_inv0 N f l hm γ1 γlock ∗ hash_tape0 α (n::ns) }}}
      f #v α
      {{{ (res:nat), RET (#res);  hash_frag0 v res γ1 ∗
                                (hash_tape0 α ns ∗ ⌜res=n⌝ ∨
                                 hash_tape0 α (n::ns)
                                )
      }}}.
  Proof.
    iIntros (Φ) "[#Hinv Ht] HΦ".
    iApply (con_hash_spec0 _ _ _ _ _ _ _ _ _ (λ res, hash_frag0 v res γ1) (hash_frag0 v n γ1) with "[$Hinv $Ht]").
    - iIntros (m) "Hauth".
      case_match.
      + iModIntro.
        iDestruct (hash_auth_duplicate_frag with "[$]") as "#?"; first done.
        by iFrame.
      + iMod (hash_auth_insert with "[$]"); first done.
        iFrame. iModIntro. by iExists _. 
    - iNext. iIntros (res) "[[??]|(%&%&%&?&%&?)]"; iApply "HΦ"; iFrame.
      simplify_eq. iFrame.
      iLeft. by iFrame.
  Qed.

  Lemma con_hash_spec_hashed_before N f l hm γ1 γlock α ns res (v:nat):
    {{{ con_hash_inv0 N f l hm γ1 γlock ∗ hash_tape0 α ns ∗ hash_frag0 v res γ1}}}
      f #v α
      {{{ RET (#res);  hash_frag0 v res γ1 ∗
                       (hash_tape0 α ns)
      }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Ht & #Hfrag) HΦ".
    iApply (con_hash_spec0 _ _ _ _ _ _ _ _ _ (λ res', ⌜res=res'⌝∗ hash_frag0 v res γ1)%I (False) with "[$Hinv $Ht]").
    - iIntros. iDestruct (hash_auth_frag_agree with "[$][//]") as "->".
      iFrame. iModIntro. by iSplit. 
    - iNext. iIntros (?) "[(?&->&?)|(%&%&%&?&%&%)]"; last done.
      iApply "HΦ".
      iFrame.
  Qed.
End test.
