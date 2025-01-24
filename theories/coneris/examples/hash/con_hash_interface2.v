From clutch.coneris Require Import coneris .

Set Default Proof Using "Type*".

Definition coll_free (m : gmap nat nat) :=
  forall k1 k2,
  is_Some (m !! k1) ->
  is_Some (m !! k2) ->
  m !!! k1 = m !!! k2 ->
  k1 = k2.


(* Definition NoDup_maps (m:gmap nat nat ) (m':gmap val (list nat)) := *)
(*   NoDup ((map_to_list m).*2 ++ concat ((map_to_list m').*2)). *)

Class con_hash2 `{!conerisGS Σ} (val_size:nat):= Con_Hash2
{
  (** * Operations *)
  init_hash2 : val;
  (* incr_counter : val; *)
  allocate_tape2 : val;
  compute_hash2 : val;
  (** * Ghost state *)
  
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  
  hash_view_gname:Type;
  hash_set_gname:Type;
  hash_tape_gname: Type;
  hash_lock_gname:Type;
  hash_view_gname': Type;
  hash_set_gname':Type;
  
  (** * Predicates *)
  con_hash_inv2 (N:namespace) (f l hm: val) (P:gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')} (γ1:hash_view_gname) (γ2: hash_set_gname) (γ3:hash_tape_gname) (γ4:hash_view_gname') (γ5:hash_set_gname') (γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape2 (α:val) (ns:list nat) (γ2: hash_set_gname) (γ3:hash_tape_gname): iProp Σ; 
  hash_tape_auth2 (m:gmap val (list nat)) (γ2 :hash_set_gname) (γ3:hash_tape_gname): iProp Σ;
  hash_auth2 (m:gmap nat nat) (γ:hash_view_gname) (γ2 : hash_set_gname) (γ4: hash_view_gname') (γ5:hash_set_gname'): iProp Σ; 
  hash_frag2 (v res:nat) (γ:hash_view_gname) (γ2 : hash_set_gname) (γ4:hash_view_gname'): iProp Σ;
  hash_set2 (s: nat) (γ2:hash_set_gname) (γ5:hash_set_gname'): iProp Σ;
  hash_set_frag2 (n:nat) (γ2: hash_set_gname)(γ5:hash_set_gname'): iProp Σ; 
  
  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_tape_timeless α ns γ2 γ3 ::
    Timeless (hash_tape2 α ns γ2 γ3 );
  #[global] hash_tape_auth_timeless m γ2 γ3::
    Timeless (hash_tape_auth2 m γ2 γ3);
  #[global] hash_auth_timeless m γ γ2 γ4 γ5::
    Timeless (hash_auth2 m γ γ2 γ4 γ5);
  #[global] hash_frag_timeless v res γ γ2 γ4::
    Timeless (hash_frag2 v res γ γ2 γ4);
  #[global] hash_set_timeless s γ2 γ5::
    Timeless (hash_set2 s γ2 γ5); 
  #[global] hash_set_frag_timeless s γ2 γ5 ::
    Timeless (hash_set_frag2 s γ2 γ5); 
  #[global] con_hash_inv_persistent N f l hm γ1 γ2 γ3 P {HP: ∀ m m', Timeless (P m m')} γ4 γ5 γ_lock ::
    Persistent (con_hash_inv2 N f l hm P γ1 γ2 γ3 γ4 γ5 γ_lock); 
  #[global] hash_frag_persistent v res γ γ2 γ4 ::
    Persistent (hash_frag2 v res γ γ2 γ4);
  (* #[global] hash_set_frag_persistent s γ2 :: *)
  (*   Persistent (hash_set_frag2 s γ2);  *)
  hash_auth_exclusive m m' γ γ2 γ4 γ5:
    hash_auth2 m γ γ2 γ4 γ5-∗ hash_auth2 m' γ γ2 γ4 γ5-∗ False;
  hash_auth_frag_agree m k v γ γ2 γ4 γ5:
    hash_auth2 m γ γ2 γ4 γ5 -∗ hash_frag2 k v γ γ2 γ4 -∗ ⌜m!!k=Some v⌝; 
  hash_auth_duplicate m k v γ γ2 γ4 γ5:
    m!!k=Some v -> hash_auth2 m γ γ2 γ4 γ5 -∗ hash_frag2 k v γ γ2 γ4;
  hash_auth_coll_free m γ γ2 γ4 γ5:
    hash_auth2 m γ γ2 γ4 γ5-∗ ⌜coll_free m⌝;
  hash_frag_frag_agree k1 k2 v1 v2 γ γ2 γ4 :
    hash_frag2 k1 v1 γ γ2 γ4 -∗ hash_frag2 k2 v2 γ γ2 γ4-∗ ⌜k1=k2<->v1=v2⌝; 
  (* hash_frag_in_hash_set γ1 γ2 v res: *)
  (*   hash_frag2 v res γ1 γ2 -∗ hash_set_frag2 res γ2 ;  *)
  (* hash_tape_in_hash_set α ns γ γ': *)
  (* hash_tape2 α ns γ γ' -∗ [∗ list] n ∈ ns, hash_set_frag2 n γ;  *)
  (* hash_set_frag_in_set s n γ: *)
  (* hash_set1 s γ -∗ hash_set_frag1 n γ -∗ ⌜n ∈ s⌝; *)
  hash_auth_insert m k v γ1 γ2 γ4 γ5:
    m!!k=None -> hash_set_frag2 v γ2 γ5 -∗ hash_auth2 m γ1 γ2 γ4 γ5 ==∗ hash_auth2 (<[k:=v]> m ) γ1 γ2 γ4 γ5  ;  
  (* hash_tape_auth_exclusive m m' γ2 γ3: *)
  (*   hash_tape_auth1 m γ2 γ3 -∗ hash_tape_auth1 m' γ2 γ3 -∗ False; *)
  (* hash_tape_auth_frag_agree m α ns γ2 γ3: *)
  (*   hash_tape_auth1 m γ2 γ3 -∗ hash_tape1 α ns γ2 γ3 -∗ ⌜m!!α=Some ns⌝; *)
  (* hash_tape_auth_insert m α γ2 γ3: *)
  (*   m!!α=None -> hash_tape_auth1 m γ2 γ3 ==∗ hash_tape_auth1 (<[α:=[]]> m) γ2 γ3 ∗ hash_tape1 α [] γ2 γ3; *)
  (* hash_tape_auth_frag_update m α ns n γ2 γ3: *)
  (* hash_set_frag1 n γ2 -∗ hash_tape_auth1 m γ2 γ3 -∗ hash_tape1 α ns γ2 γ3 ==∗ *)
  (* hash_tape_auth1 (<[α:=ns++[n]]> m) γ2 γ3 ∗ hash_tape1 α (ns ++ [n]) γ2 γ3; *) 
  (* hash_set_valid s γ: *)
  (*   hash_set1 s γ -∗ ⌜∀ n, n∈s -> (n<=val_size)%nat⌝; *)
  hash_tape_valid α ns γ2 γ3 :
    hash_tape2 α ns γ2 γ3 -∗ ⌜Forall (λ x, x<=val_size)%nat ns⌝; 
  hash_tape_exclusive α ns ns' γ2 γ3 :
      hash_tape2 α ns γ2 γ3 -∗ hash_tape2 α ns' γ2 γ3  -∗ False; 

  
  hash_tape_presample m γ γ_set γ_set' α ns s (ε εO:nonnegreal) E:
    (INR s + εO * (val_size + 1 - INR s) <= ε * (val_size + 1))%R ->
    hash_tape_auth2 m γ_set γ -∗ hash_tape2 α ns γ_set γ-∗ ↯ ε -∗
    hash_set2 s γ_set γ_set'-∗
    state_update E E (∃ (n:fin(S val_size)), 
          (  hash_set2 (s+1)%nat γ_set γ_set' ∗ ↯ εO
          )∗
          hash_tape_auth2 (<[α:=ns++[fin_to_nat n]]>m) γ_set γ ∗
          hash_tape2 α (ns++[fin_to_nat n]) γ_set γ ∗ hash_set_frag2 (fin_to_nat n) γ_set γ_set'
      );

  con_hash_presample2  N f l hm P {HP: ∀ m m', Timeless (P m m')} γ_hv γ_set γ_tape γ_hv' γ_set' γ_lock Q
    E  :
    ↑N ⊆ E ->
    con_hash_inv2 N f l hm P γ_hv γ_set γ_tape γ_hv' γ_set' γ_lock -∗
    (∀ m m', P m m'  -∗
             hash_tape_auth2 m' γ_set γ_tape -∗
             state_update (E∖↑N) (E∖↑N)
             (∃ m'', P m m'' ∗ hash_tape_auth2 m'' γ_set γ_tape ∗ Q m m' m'')
    ) -∗
    state_update E E (
        ∃ m m' m'', Q m m' m''
      ) ; 

  con_hash_init2 N P {HP: ∀ m m', Timeless (P m m')}:
    {{{ P ∅ ∅ }}}
      init_hash2 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_lock, con_hash_inv2 N f l hm P γ1 γ2 γ3 γ4 γ5 γ_lock ∗
                                                  hash_set2 0%nat γ2 γ5
      }}}; 

  con_hash_alloc_tape2 N f l hm P {HP: ∀ m m', Timeless (P m m')} γ1 γ2 γ3 γ4 γ5 γ_lock Q:
  {{{ con_hash_inv2 N f l hm P γ1 γ2 γ3 γ4 γ5 γ_lock ∗
      (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ -∗ |={⊤∖↑N}=> P m (<[α:=[]]>m') ∗ Q α)
  }}}
      allocate_tape2 #()
      {{{ (α: val), RET α; hash_tape2 α [] γ2 γ3 ∗ Q α }}};  

  con_hash_spec2 N f l hm P {HP: ∀ m m', Timeless (P m m')} γ1 γ2 γ3 γ4 γ5 γ_lock Q1 Q2 α ns (v:nat):
  {{{ con_hash_inv2 N f l hm P γ1 γ2 γ3 γ4 γ5 γ_lock ∗ hash_tape2 α (ns) γ2 γ3∗
      ( ∀ m m', P m m' -∗
                hash_auth2 m γ1 γ2 γ4 γ5-∗
                ⌜m'!!α=Some ns⌝ -∗
                |={⊤∖↑N}=>
             match m!!v with
             | Some res => P m m' ∗ hash_auth2 m γ1 γ2 γ4 γ5 ∗ Q1 res
             | None => ∃ n ns', ⌜n::ns'=ns⌝ ∗ P (<[v:=n]> m) (<[α:=ns']> m')∗ hash_auth2 (<[v:=n]> m) γ1 γ2 γ4 γ5 ∗
                                 Q2
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (hash_tape2 α (ns) γ2 γ3 ∗ Q1 res ∨
                                 ∃ n ns', ⌜n::ns'=ns⌝ ∗ hash_tape2 α ns' γ2 γ3 ∗ ⌜res=n⌝ ∗ Q2 
                                )
      }}};
}.


Section test.
  Context `{conerisGS Σ, !con_hash2 val_size}.
  Definition hash_tape2' α ns γ2 γ3 γ5:= (hash_tape2 α ns γ2 γ3 ∗ [∗ list] n∈ns, hash_set_frag2 n γ2 γ5)%I.
                                                    

  Lemma con_hash_presample_test N f l hm γ1 γ2 γ3 γ4 γ5 γlock  E (ε εI εO:nonnegreal) ns α s :
    ↑N⊆E ->
    (INR s+ εO * (val_size + 1 - INR s) <= ε * (val_size + 1))%R ->
    con_hash_inv2 N f l hm (λ _ _, True) γ1 γ2 γ3 γ4 γ5 γlock -∗
    hash_tape2' α ns γ2 γ3 γ5-∗
    ↯ ε -∗
    hash_set2 s γ2 γ5-∗
    state_update E E (∃ (n:fin (S val_size)),
          hash_tape2' α (ns++[fin_to_nat n]) γ2 γ3 γ5 ∗
          ( hash_set2 (s+1)%nat γ2 γ5∗ ↯ εO
          )
      ).
  Proof.
    iIntros (Hsubset Hineq) "#Hinv [Ht Hfrag] Herr Hs".
    iMod (con_hash_presample2 _ _ _ _ _ _ _ _ _ _ _
            (λ m m' m'', (∃ n : fin (S val_size), hash_tape2 α (ns ++ [fin_to_nat n]) γ2 γ3 ∗
                                                  ( hash_set2 (s +1)%nat γ2 γ5 ∗ ↯ εO) ∗ hash_set_frag2 (fin_to_nat n) _ _))%I with "[//][-Hfrag]") as "Hcont"; first done.
    - iIntros (_ ?) "_ Hauth".
      by iMod (hash_tape_presample with "[$][$][$][$]") as "(%&[$$]&$&$&?)". 
    - iFrame. iDestruct "Hcont" as "(%&%&%&%&$&$&$)". by iModIntro.
  Qed.
  
    
  Lemma con_hash_spec_test2 N f l hm γ1 γ2 γ3 γ4 γ5 γlock α n ns (v:nat):
    {{{ con_hash_inv2 N f l hm (λ _ _, True) γ1 γ2 γ3 γ4 γ5 γlock ∗ hash_tape2' α (n::ns) γ2 γ3 γ5 }}}
      f #v α
      {{{ (res:nat), RET (#res);  hash_frag2 v res γ1 γ2 γ4 ∗
                                (hash_tape2' α ns γ2 γ3 γ5 ∗ ⌜res=n⌝ ∨
                                 hash_tape2' α (n::ns) γ2 γ3 γ5
                                )
      }}}.
  Proof.
    iIntros (Φ) "[#Hinv [Ht Hlis]] HΦ".
    iApply (con_hash_spec2 _ _ _ _ _ _ _ _ _ _ _ (λ res, hash_frag2 v res γ1 γ2 γ4 ∗ [∗ list] n0 ∈ (n :: ns), hash_set_frag2 n0 γ2 γ5)%I (hash_frag2 v n γ1 γ2 γ4 ∗ [∗ list] n0 ∈ (ns), hash_set_frag2 n0 γ2 γ5) with "[$Hinv $Ht Hlis]").
    - iIntros (??) "_ Hauth %".
      case_match.
      + iDestruct (hash_auth_duplicate with "[$]") as "#$"; first done. by iFrame.
      + iDestruct "Hlis" as "[H1 Hlis]".
        iMod (hash_auth_insert with "[$][$]") as "H"; first done.
        iDestruct (hash_auth_duplicate with "[$]") as "#$"; first by rewrite lookup_insert.
        iFrame. iModIntro. iExists _. done.
    - iNext. iIntros (res) "[(?&?&?)|(%&%&%&?&%&H&?)]".
      + iApply "HΦ". iFrame. iRight. iFrame.
      + iApply "HΦ". simplify_eq. iFrame "H". iLeft. by iFrame.
  Qed.

  Lemma con_hash_spec_hashed_before2 N f l hm γ1 γ2 γ3 γ4 γ5 γlock α ns res (v:nat):
    {{{ con_hash_inv2 N f l hm (λ _ _, True) γ1 γ2 γ3 γ4 γ5 γlock ∗ hash_tape2' α ns γ2 γ3 γ5 ∗ hash_frag2 v res γ1 γ2 γ4}}}
      f #v α
      {{{ RET (#res);  hash_frag2 v res γ1 γ2 γ4 ∗
                       (hash_tape2' α ns γ2 γ3 γ5)
      }}}.
  Proof. 
    iIntros (Φ) "(#Hinv & [Ht ?] & #Hf) HΦ".
    iApply (con_hash_spec2 _ _ _ _ _ _ _ _ _ _ _(λ res' , ⌜res=res'⌝ ∗ hash_frag2 v res γ1 γ2 γ4  )%I (False) with "[$Hinv $Ht]").
    - iIntros (??) "_ Hauth %".
      case_match.
      + iDestruct (hash_auth_frag_agree with "[$][$]") as "%".
        simplify_eq. iDestruct (hash_auth_duplicate with "[$]") as "#$"; first done.
        iFrame. by done. 
      + iDestruct (hash_auth_frag_agree with "[$][$]") as "%".
        simplify_eq.
    - iNext. iIntros (res') "[[?[->?]]|(%&%&%&?&?&%)]".
      + iApply "HΦ". iFrame.
      + done.
  Qed.
  
End test.
