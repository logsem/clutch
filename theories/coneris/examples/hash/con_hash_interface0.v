From clutch.coneris Require Import coneris .

Set Default Proof Using "Type*".


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
  
  (* hash_view_gname:Type; *)
  hash_tape_gname: Type;
  hash_lock_gname:Type;
  
  (** * Predicates *)
  con_hash_inv0 (N:namespace) (f l hm: val) (P:gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')}
    (R:gmap nat nat -> iProp Σ) {HR: ∀ m, Timeless (R m )} (γ:hash_tape_gname) (γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape0 (α:val) (ns:list nat) (γ:hash_tape_gname): iProp Σ;
  hash_tape_auth0 (m:gmap val (list nat)) (γ:hash_tape_gname) :iProp Σ;
  (* hash_auth0 (m:gmap nat nat) (γ2:hash_view_gname) : iProp Σ; *)
  (* hash_frag0 (v res:nat) (γ:hash_view_gname): iProp Σ; *)
  
  (** * General properties of the predicates *)
  #[global] hash_tape_timeless α ns γ::
    Timeless (hash_tape0 α ns γ); 
  #[global] hash_tape_auth_timeless m γ::
    Timeless (hash_tape_auth0 m γ);
  (* #[global] hash_map_timeless m γ :: *)
  (*   Timeless (hash_auth0 m γ); *)
  (* #[global] hash_frag_timeless v res γ :: *)
  (*   Timeless (hash_frag0 v res γ); *)
  #[global] con_hash_inv_persistent N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock ::
    Persistent (con_hash_inv0 N f l hm P R γ_tape γ_lock); 
  (* #[global] hash_frag_persistent v res γ :: *)
  (*   Persistent (hash_frag0 v res γ); *)
  
  hash_tape_valid α ns γ:
    hash_tape0 α ns γ-∗ ⌜Forall (λ x, x<=val_size)%nat ns⌝;
  hash_tape_exclusive α ns ns' γ:
    hash_tape0 α ns γ-∗ hash_tape0 α ns' γ-∗ False;
  (* hash_tape_auth_exclusive m m' γ: *)
  (*   hash_tape_auth0 m γ -∗ hash_tape_auth0 m' γ -∗ False; *)
  hash_tape_auth_frag_agree m α ns γ:
    hash_tape_auth0 m γ  -∗ hash_tape0 α ns γ -∗ ⌜m!!α=Some ns⌝;
  (* hash_tape_auth_alloc m α γ: *)
  (*   m!!α=None -> hash_tape_auth0 m γ ==∗ hash_tape_auth0 (<[α:=[]]> m) γ ∗ hash_tape0 α [] γ; *)
  hash_tape_presample N m γ γ_lock f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} α ns ε ε2 E:
  ↑(N.@"rand")⊆E ->
    (∀ x : fin (S val_size), (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    con_hash_inv0 N f l hm P R γ γ_lock -∗
    hash_tape_auth0 m γ -∗ hash_tape0 α ns γ -∗ ↯ ε -∗
    state_update E E (∃ n, 
          ↯ (ε2 n) ∗
          hash_tape_auth0 (<[α:=ns++[fin_to_nat n]]>m) γ ∗
          hash_tape0 α (ns++[fin_to_nat n]) γ); 
  (* hash_auth_exclusive m m' γ: *)
  (*   hash_auth0 m γ -∗ hash_auth0 m' γ -∗ False; *)
  (* hash_frag_frag_agree k v1 v2 γ : *)
  (*   hash_frag0 k v1 γ -∗ hash_frag0 k v2 γ -∗ ⌜v1=v2⌝; *)
  (* hash_auth_duplicate_frag m k v γ: *)
  (*   m!!k=Some v -> hash_auth0 m γ -∗ hash_frag0 k v γ; *)
  (* hash_auth_insert m k v γ: *)
  (*   m!!k=None -> hash_auth0 m γ ==∗ (hash_auth0 (<[k:=v]> m) γ ∗ hash_frag0 k v γ); *)
                      

  con_hash_presample0 N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ γ_lock Q
    E  :
    ↑(N.@"hash") ⊆ E ->
    con_hash_inv0 N f l hm P R γ γ_lock -∗
    (∀ m m', P m m'  -∗
             hash_tape_auth0 m' γ -∗
             state_update (E∖↑(N.@"hash")) (E∖↑(N.@"hash"))
             (∃ m'', P m m'' ∗ hash_tape_auth0 m'' γ ∗ Q m m' m'')
    ) -∗
    state_update E E (
        ∃ m m' m'', Q m m' m''
      ); 

  con_hash_init0 N P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} :
    {{{ P ∅ ∅ ∗ R ∅}}}
      init_hash0 #()
      {{{ (f:val), RET f; ∃ l hm γ_tape γ_lock, con_hash_inv0 N f l hm P R γ_tape γ_lock }}}; 

  con_hash_alloc_tape0 N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock Q:
  {{{ con_hash_inv0 N f l hm P R γ_tape γ_lock ∗
      (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ -∗ |={⊤∖↑N.@"hash"}=> P m (<[α:=[]]>m') ∗ Q α)
  }}}
      allocate_tape0 #()
      {{{ (α: val), RET α; hash_tape0 α [] γ_tape ∗ Q α }}}; 
  
  con_hash_spec0 N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv0 N f l hm P R γ_tape γ_lock ∗ 
      ( ∀ m m', R m -∗ P m m' -∗ hash_tape_auth0 m' γ_tape -∗ state_update (⊤∖↑N.@"hash") (⊤∖↑N.@"hash")
             match m!!v with
             | Some res => R m ∗ P m m' ∗ hash_tape_auth0 m' γ_tape ∗ Q1 res
             | None => ∃ n ns, hash_tape0 α (n::ns) γ_tape ∗ P m (<[α:=n::ns]> m') ∗ hash_tape_auth0 (<[α:=n::ns]> m') γ_tape ∗
                              (∀ m'', P m m'' -∗  ⌜m''!!α=Some (n::ns)⌝
                                      ={⊤∖↑N.@"hash"}=∗ R (<[v:=n]> m) ∗ P (<[v:=n]> m) (<[α:=ns]> m'') ∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ n ns, hash_tape0 α ns γ_tape ∗ ⌜res=n⌝ ∗ Q2 n ns
                                )
      }}};
  (* con_hash_spec_hashed_before0 f l hm γ1 γ2 γlock α ns res (v:nat): *)
  (*   {{{ con_hash_inv0 f l hm γ1 γ2 γlock ∗ hash_tape0 α ns ∗ hash_frag0 v res γ1}}} *)
  (*     f #v α *)
  (*     {{{ RET (#res);  hash_frag0 v res γ1 ∗ *)
  (*                      (hash_tape0 α ns) *)
  (*     }}} *)
}.

(* Section test. *)
(*   Context `{conerisGS Σ, !con_hash0 val_size}. *)
(*   Lemma con_hash_spec0' N f l hm γ1 γlock α n ns (v:nat): *)
(*     {{{ con_hash_inv0 N f l hm γ1 γlock ∗ hash_tape0 α (n::ns) }}} *)
(*       f #v α *)
(*       {{{ (res:nat), RET (#res);  hash_frag0 v res γ1 ∗ *)
(*                                 (hash_tape0 α ns ∗ ⌜res=n⌝ ∨ *)
(*                                  hash_tape0 α (n::ns) *)
(*                                 ) *)
(*       }}}. *)
(*   Proof. *)
(*     iIntros (Φ) "[#Hinv Ht] HΦ". *)
(*     iApply (con_hash_spec0 _ _ _ _ _ _ _ _ _ (λ res, hash_frag0 v res γ1) (hash_frag0 v n γ1) with "[$Hinv $Ht]"). *)
(*     - iIntros (m) "Hauth". *)
(*       case_match. *)
(*       + iModIntro. *)
(*         iDestruct (hash_auth_duplicate_frag with "[$]") as "#?"; first done. *)
(*         by iFrame. *)
(*       + iMod (hash_auth_insert with "[$]"); first done. *)
(*         iFrame. iModIntro. by iExists _.  *)
(*     - iNext. iIntros (res) "[[??]|(%&%&%&?&%&?)]"; iApply "HΦ"; iFrame. *)
(*       simplify_eq. iFrame. *)
(*       iLeft. by iFrame. *)
(*   Qed. *)

(*   Lemma con_hash_spec_hashed_before N f l hm γ1 γlock α ns res (v:nat): *)
(*     {{{ con_hash_inv0 N f l hm γ1 γlock ∗ hash_tape0 α ns ∗ hash_frag0 v res γ1}}} *)
(*       f #v α *)
(*       {{{ RET (#res);  hash_frag0 v res γ1 ∗ *)
(*                        (hash_tape0 α ns) *)
(*       }}}. *)
(*   Proof. *)
(*     iIntros (Φ) "(#Hinv & Ht & #Hfrag) HΦ". *)
(*     iApply (con_hash_spec0 _ _ _ _ _ _ _ _ _ (λ res', ⌜res=res'⌝∗ hash_frag0 v res γ1)%I (False) with "[$Hinv $Ht]"). *)
(*     - iIntros. iDestruct (hash_auth_frag_agree with "[$][//]") as "->". *)
(*       iFrame. iModIntro. by iSplit.  *)
(*     - iNext. iIntros (?) "[(?&->&?)|(%&%&%&?&%&%)]"; last done. *)
(*       iApply "HΦ". *)
(*       iFrame. *)
(*   Qed. *)
(* End test. *)
