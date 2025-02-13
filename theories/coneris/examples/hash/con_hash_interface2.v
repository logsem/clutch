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
  con_hash_inv2 (N:namespace) (f l hm: val)  (R:gmap nat nat -> iProp Σ) {HR: ∀ m, Timeless (R m )} (γ1:hash_view_gname) (γ2: hash_set_gname) (γ3:hash_tape_gname) (γ4:hash_view_gname') (γ5:hash_set_gname') (γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape2 (α:val) (ns:list nat) (γ2: hash_set_gname) (γ3:hash_tape_gname): iProp Σ; 
  hash_auth2 (m:gmap nat nat) (γ:hash_view_gname) (γ2 : hash_set_gname) (γ4: hash_view_gname') (γ5:hash_set_gname'): iProp Σ; 
  hash_frag2 (v res:nat) (γ:hash_view_gname) (γ2 : hash_set_gname) (γ4:hash_view_gname'): iProp Σ;
  hash_set2 (s: nat) (γ2:hash_set_gname) (γ5:hash_set_gname'): iProp Σ;
  hash_set_frag2 (n:nat) (γ2: hash_set_gname)(γ5:hash_set_gname'): iProp Σ; 
  
  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_tape_timeless α ns γ2 γ3 ::
    Timeless (hash_tape2 α ns γ2 γ3 );
  #[global] hash_auth_timeless m γ γ2 γ4 γ5::
    Timeless (hash_auth2 m γ γ2 γ4 γ5);
  #[global] hash_frag_timeless v res γ γ2 γ4::
    Timeless (hash_frag2 v res γ γ2 γ4);
  #[global] hash_set_timeless s γ2 γ5::
    Timeless (hash_set2 s γ2 γ5); 
  #[global] hash_set_frag_timeless s γ2 γ5 ::
    Timeless (hash_set_frag2 s γ2 γ5); 
  #[global] con_hash_inv_persistent N f l hm γ1 γ2 γ3 R {HR: ∀ m, Timeless (R m )}γ4 γ5 γ_lock ::
    Persistent (con_hash_inv2 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock); 
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

  
  hash_tape_presample N f l hm R {HR: ∀ m, Timeless (R m )} γ_hv γ_set γ_hv' γ γ_set' γ_lock α ns s (ε εO:nonnegreal) E:
  ↑(N)⊆E ->
  (INR s + εO * (val_size + 1 - INR s) <= ε * (val_size + 1))%R ->
  con_hash_inv2 N f l hm R γ_hv γ_set γ γ_hv' γ_set' γ_lock -∗
    hash_tape2 α ns γ_set γ-∗ ↯ ε -∗
    hash_set2 s γ_set γ_set'-∗
    state_update E E (∃ (n:fin(S val_size)), 
          (  hash_set2 (s+1)%nat γ_set γ_set' ∗ ↯ εO
          )∗
          hash_tape2 α (ns++[fin_to_nat n]) γ_set γ ∗ hash_set_frag2 (fin_to_nat n) γ_set γ_set'
      );

  con_hash_init2 N R {HR: ∀ m, Timeless (R m )}:
    {{{ R ∅}}}
      init_hash2 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_lock, con_hash_inv2 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock ∗
                                                  hash_set2 0%nat γ2 γ5
      }}}; 

  con_hash_alloc_tape2 N f l hm R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ4 γ5 γ_lock:
  {{{ con_hash_inv2 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock 
  }}}
      allocate_tape2 #()
      {{{ (α: val), RET α; hash_tape2 α [] γ2 γ3}}};  

  con_hash_spec2  N f l hm R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ4 γ5 γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv2 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock ∗ 
      ( ∀ m, R m -∗  hash_auth2 m γ1 γ2 γ4 γ5-∗ state_update (⊤) (⊤)
             match m!!v with
             | Some res => R m ∗ hash_auth2 m γ1 γ2 γ4 γ5∗ Q1 res
             | None => ∃ n ns, hash_tape2 α (n::ns) γ2 γ3 ∗ 
                              (hash_tape2 α (ns) γ2 γ3 
                                      ={⊤}=∗ R (<[v:=n]> m) ∗ 
                                      hash_auth2 (<[v:=n]> m) γ1 γ2 γ4 γ5∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns,  Q2 res ns
                                )
      }}}
;
}.


Section test.
  Context `{conerisGS Σ, !con_hash2 val_size}.
  Definition hash_tape2' α ns γ2 γ3 γ5:= (hash_tape2 α ns γ2 γ3 ∗ [∗ list] n∈ns, hash_set_frag2 n γ2 γ5)%I.
                 
    
  Lemma con_hash_spec_test2 N f l hm γ1 γ2 γ3 γ4 γ5 γlock α n ns (v:nat):
    {{{ con_hash_inv2 N f l hm (λ _, True) γ1 γ2 γ3 γ4 γ5 γlock ∗ hash_tape2' α (n::ns) γ2 γ3 γ5 }}}
      f #v α
      {{{ (res:nat), RET (#res);  hash_frag2 v res γ1 γ2 γ4 ∗
                                (hash_tape2' α ns γ2 γ3 γ5 ∗ ⌜res=n⌝ ∨
                                 hash_tape2' α (n::ns) γ2 γ3 γ5
                                )
      }}}.
  Proof.
    iIntros (Φ) "[#Hinv [Ht Hlis]] HΦ".
    iApply (con_hash_spec2 _ _ _ _ _ _ _ _ _ _ _ (λ res, hash_tape2 _ _ _ _ ∗ hash_frag2 v res γ1 γ2 γ4 ∗ [∗ list] n0 ∈ (n :: ns), hash_set_frag2 n0 γ2 γ5)%I (λ n' ns', ⌜n=n'⌝ ∗ ⌜ns=ns'⌝ ∗ hash_tape2 _ _ _ _ ∗ hash_frag2 v n γ1 γ2 γ4 ∗ [∗ list] n0 ∈ (ns), hash_set_frag2 n0 γ2 γ5)%I with "[$Hinv Ht Hlis]").
    - iIntros (?) "_  Hauth".
      case_match.
      + iDestruct (hash_auth_duplicate with "[$]") as "#$"; first done. by iFrame.
      + iDestruct "Hlis" as "[H1 Hlis]".
        iMod (hash_auth_insert with "[$][$]") as "H"; first done.
        iDestruct (hash_auth_duplicate with "[$]") as "#$"; first by rewrite lookup_insert.
        iFrame. iModIntro. iIntros. by iFrame.
    - iNext. iIntros (res) "[(?&?&?)|(%&->&->&?&?&?)]".
      + iApply "HΦ". iFrame. iRight. iFrame.
      + iApply "HΦ". simplify_eq. iFrame. iLeft. by iFrame. 
  Qed.

  Lemma con_hash_spec_hashed_before2 N f l hm γ1 γ2 γ3 γ4 γ5 γlock α ns res (v:nat):
    {{{ con_hash_inv2 N f l hm (λ _, True) γ1 γ2 γ3 γ4 γ5 γlock ∗ hash_tape2' α ns γ2 γ3 γ5 ∗ hash_frag2 v res γ1 γ2 γ4}}}
      f #v α
      {{{ RET (#res);  hash_frag2 v res γ1 γ2 γ4 ∗
                       (hash_tape2' α ns γ2 γ3 γ5)
      }}}.
  Proof. 
    iIntros (Φ) "(#Hinv & [Ht ?] & #Hf) HΦ".
    iApply (con_hash_spec2 _ _ _ _ _ _ _ _ _ _ _ (λ res' , ⌜res=res'⌝ ∗ hash_frag2 v res γ1 γ2 γ4 ∗ hash_tape2 _ _ _ _ )%I (λ _ _, ⌜False⌝)%I with "[$Hinv Ht]").
    - iIntros (?) "_ Hauth".
      case_match.
      + iDestruct (hash_auth_frag_agree with "[$][$]") as "%".
        simplify_eq. iDestruct (hash_auth_duplicate with "[$]") as "#$"; first done.
        iFrame. by done. 
      + iDestruct (hash_auth_frag_agree with "[$][$]") as "%".
        simplify_eq.
    - iNext. iIntros (res') "[[->[??]]|(%&[])]".
      iApply "HΦ". iFrame.
  Qed.
  
End test.
