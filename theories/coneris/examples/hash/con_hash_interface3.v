From clutch.coneris Require Import coneris .

Set Default Proof Using "Type*".

Definition coll_free (m : gmap nat nat) :=
  forall k1 k2,
  is_Some (m !! k1) ->
  is_Some (m !! k2) ->
  m !!! k1 = m !!! k2 ->
  k1 = k2.

Program Definition amortized_error (val_size:nat) (max_hash_size:nat) (H:0<max_hash_size): nonnegreal :=
    mknonnegreal ((max_hash_size-1) /(2*(val_size + 1)))%R _.
Next Obligation.
  intros val_size max_hash_size max_hash_size_pos.
    pose proof (pos_INR val_size) as H.
    pose proof (pos_INR max_hash_size) as H'.
    apply Rcomplements.Rdiv_le_0_compat; try lra.
    assert (1 <= INR max_hash_size)%R; try lra.
    replace 1%R with (INR 1); last simpl; [by apply le_INR|done].
  Qed.
  
Class con_hash3 `{!conerisGS Σ} (val_size:nat) (max_hash_size:nat) (Hpos:0<max_hash_size):= Con_Hash3
{
  (** * Operations *)
  init_hash3 : val;
  (* incr_counter : val; *)
  allocate_tape3 : val;
  compute_hash3 : val;
  (** * Ghost state *)
  
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  
  hash_view_gname:Type;
  hash_set_gname:Type;
  hash_tape_gname: Type;
  hash_lock_gname:Type;
  hash_view_gname': Type;
  hash_set_gname':Type;
  hash_token_gname:Type;
  
  (** * Predicates *)
  con_hash_inv3 (N:namespace) (f l hm: val) (P:gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')}  (R:gmap nat nat -> iProp Σ) {HR: ∀ m, Timeless (R m )} (γ1:hash_view_gname) (γ2: hash_set_gname) (γ3:hash_tape_gname) (γ4:hash_view_gname') (γ5:hash_set_gname') (γ6: hash_token_gname) (γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape3 (α:val) (ns:list nat) (γ2: hash_set_gname) (γ3:hash_tape_gname): iProp Σ; 
  hash_tape_auth3 (m:gmap val (list nat)) (γ2 :hash_set_gname) (γ3:hash_tape_gname): iProp Σ;
  hash_auth3 (m:gmap nat nat) (γ:hash_view_gname) (γ2 : hash_set_gname) (γ4: hash_view_gname') (γ5:hash_set_gname'): iProp Σ; 
  hash_frag3 (v res:nat) (γ:hash_view_gname) (γ2 : hash_set_gname) (γ4:hash_view_gname'): iProp Σ;
  hash_set3 (s: nat) (γ2:hash_set_gname) (γ5:hash_set_gname') (γ6: hash_token_gname): iProp Σ;
  hash_set_frag3 (n:nat) (γ2: hash_set_gname)(γ5:hash_set_gname'): iProp Σ;
  hash_token3 (n:nat) (γ6:hash_token_gname):iProp Σ; 
  
  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_tape_timeless α ns γ2 γ3 ::
    Timeless (hash_tape3 α ns γ2 γ3 );
  #[global] hash_tape_auth_timeless m γ2 γ3::
    Timeless (hash_tape_auth3 m γ2 γ3);
  #[global] hash_auth_timeless m γ γ2 γ4 γ5::
    Timeless (hash_auth3 m γ γ2 γ4 γ5);
  #[global] hash_frag_timeless v res γ γ2 γ4::
    Timeless (hash_frag3 v res γ γ2 γ4);
  #[global] hash_set_timeless s γ2 γ5 γ6::
    Timeless (hash_set3 s γ2 γ5 γ6);
  #[global] hash_set_frag_timeless s γ2 γ5 ::
    Timeless (hash_set_frag3 s γ2 γ5); 
  #[global] hash_token_timeless s γ6 ::
    Timeless (hash_token3 s γ6); 
  #[global] con_hash_inv_persistent N f l hm γ1 γ2 γ3 P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ4 γ5 γ6 γ_lock ::
    Persistent (con_hash_inv3 N f l hm P R γ1 γ2 γ3 γ4 γ5 γ6 γ_lock); 
  #[global] hash_frag_persistent v res γ γ2 γ4 ::
    Persistent (hash_frag3 v res γ γ2 γ4);
  (* #[global] hash_set_frag_persistent s γ2 :: *)
  (*   Persistent (hash_set_frag2 s γ2);  *)
  hash_auth_exclusive m m' γ γ2 γ4 γ5:
    hash_auth3 m γ γ2 γ4 γ5-∗ hash_auth3 m' γ γ2 γ4 γ5-∗ False;
  hash_auth_frag_agree m k v γ γ2 γ4 γ5:
    hash_auth3 m γ γ2 γ4 γ5 -∗ hash_frag3 k v γ γ2 γ4 -∗ ⌜m!!k=Some v⌝; 
  hash_auth_duplicate m k v γ γ2 γ4 γ5:
    m!!k=Some v -> hash_auth3 m γ γ2 γ4 γ5 -∗ hash_frag3 k v γ γ2 γ4; 
  hash_auth_coll_free m γ γ2 γ4 γ5:
    hash_auth3 m γ γ2 γ4 γ5-∗ ⌜coll_free m⌝;
  hash_frag_frag_agree k1 k2 v1 v2 γ γ2 γ4 :
    hash_frag3 k1 v1 γ γ2 γ4 -∗ hash_frag3 k2 v2 γ γ2 γ4-∗ ⌜k1=k2<->v1=v2⌝; 
  (* hash_frag_in_hash_set γ1 γ2 v res: *)
  (*   hash_frag2 v res γ1 γ2 -∗ hash_set_frag2 res γ2 ;  *)
  (* hash_tape_in_hash_set α ns γ γ': *)
  (* hash_tape2 α ns γ γ' -∗ [∗ list] n ∈ ns, hash_set_frag2 n γ;  *)
  (* hash_set_frag_in_set s n γ: *)
  (* hash_set1 s γ -∗ hash_set_frag1 n γ -∗ ⌜n ∈ s⌝; *)
  hash_auth_insert m k v γ1 γ2 γ4 γ5:
    m!!k=None -> hash_set_frag3 v γ2 γ5 -∗ hash_auth3 m γ1 γ2 γ4 γ5 ==∗ hash_auth3 (<[k:=v]> m ) γ1 γ2 γ4 γ5  ;  
  (* hash_tape_auth_exclusive m m' γ2 γ3: *)
  (*   hash_tape_auth1 m γ2 γ3 -∗ hash_tape_auth1 m' γ2 γ3 -∗ False; *)
  hash_tape_auth_frag_agree m α ns γ2 γ3:
    hash_tape_auth3 m γ2 γ3 -∗ hash_tape3 α ns γ2 γ3 -∗ ⌜m!!α=Some ns⌝;
  (* hash_tape_auth_insert m α γ2 γ3: *)
  (*   m!!α=None -> hash_tape_auth1 m γ2 γ3 ==∗ hash_tape_auth1 (<[α:=[]]> m) γ2 γ3 ∗ hash_tape1 α [] γ2 γ3; *)
  (* hash_tape_auth_frag_update m α ns n γ2 γ3: *)
  (* hash_set_frag1 n γ2 -∗ hash_tape_auth1 m γ2 γ3 -∗ hash_tape1 α ns γ2 γ3 ==∗ *)
  (* hash_tape_auth1 (<[α:=ns++[n]]> m) γ2 γ3 ∗ hash_tape1 α (ns ++ [n]) γ2 γ3; *) 
  (* hash_set_valid s γ: *)
  (*   hash_set1 s γ -∗ ⌜∀ n, n∈s -> (n<=val_size)%nat⌝; *)
  hash_tape_valid α ns γ2 γ3 :
    hash_tape3 α ns γ2 γ3 -∗ ⌜Forall (λ x, x<=val_size)%nat ns⌝; 
  hash_tape_exclusive α ns ns' γ2 γ3 :
    hash_tape3 α ns γ2 γ3 -∗ hash_tape3 α ns' γ2 γ3  -∗ False;
  hash_token_split n n' γ6:
  hash_token3 (n+n') γ6 ⊣⊢hash_token3 n γ6 ∗ hash_token3 n' γ6;

  
  hash_tape_presample N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} m γ_hv γ_set γ_hv' γ_token γ γ_set' γ_lock α ns  E:
  ↑(N.@"rand")⊆E ->
  ↑(N.@"err")⊆E ->
  con_hash_inv3 N f l hm P R γ_hv γ_set γ γ_hv' γ_set' γ_token γ_lock -∗
  hash_tape_auth3 m γ_set γ -∗
  hash_tape3 α ns γ_set γ-∗
  ↯ (amortized_error val_size max_hash_size Hpos) -∗
  hash_token3 1 γ_token-∗
    (* hash_set3 s γ_set γ_set' γ6-∗ *)
    state_update E E (∃ (n:fin(S val_size)), 
          (* ( hash_set3 (s+1)%nat γ_set γ_set' γ6 )∗ *)
          hash_tape_auth3 (<[α:=ns++[fin_to_nat n]]>m) γ_set γ ∗
          hash_tape3 α (ns++[fin_to_nat n]) γ_set γ ∗ hash_set_frag3 (fin_to_nat n) γ_set γ_set'
      ); 

  con_hash_presample3  N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ_hv γ_set γ_tape γ_hv' γ_set' γ_token γ_lock Q
    E  :
  ↑(N.@"hash") ⊆ E ->
  (* ↑(N.@"err") ⊆ E -> *)
    con_hash_inv3 N f l hm P R γ_hv γ_set γ_tape γ_hv' γ_set' γ_token γ_lock -∗
    (∀ m m', P m m'  -∗
               (* hash_set3 s γ_set γ_set' γ_token -∗ *)
             hash_tape_auth3 m' γ_set γ_tape -∗
             state_update (E∖↑(N.@"hash")) (E∖↑(N.@"hash"))
             (∃ m'' , P m m'' ∗ hash_tape_auth3 m'' γ_set γ_tape ∗  Q m m' m'' )
    ) -∗
    state_update E E (
        ∃ m m' m''  , Q m m' m'' 
      ) ; 

  con_hash_init3 N P {HP: ∀ m m', Timeless (P m m')}R {HR: ∀ m, Timeless (R m )} :
    {{{ P ∅ ∅ ∗ R ∅}}}
      init_hash3 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_token γ_lock, con_hash_inv3 N f l hm P R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗  hash_token3 max_hash_size γ_token
      }}}; 

  con_hash_alloc_tape3 N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ4 γ5 γ_token γ_lock Q:
  {{{ con_hash_inv3 N f l hm P R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗
      (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ -∗ |={⊤∖↑N.@"hash"}=> P m (<[α:=[]]>m') ∗ Q α)
  }}}
      allocate_tape3 #()
      {{{ (α: val), RET α; hash_tape3 α [] γ2 γ3 ∗ Q α }}};  

  con_hash_spec3 N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ4 γ5 γ_token γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv3 N f l hm P R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗ 
      ( ∀ m m', R m -∗ P m m' -∗ hash_tape_auth3 m' γ2 γ3 -∗ hash_auth3 m γ1 γ2 γ4 γ5-∗ state_update (⊤∖↑N.@"hash") (⊤∖↑N.@"hash")
             match m!!v with
             | Some res => R m ∗ P m m' ∗hash_tape_auth3 m' γ2 γ3 ∗ hash_auth3 m γ1 γ2 γ4 γ5∗ Q1 res
             | None => ∃ n ns, hash_tape3 α (n::ns) γ2 γ3 ∗ P m (<[α:=n::ns]> m') ∗ hash_tape_auth3 (<[α:=n::ns]> m') γ2 γ3 ∗
                              (∀ m'', P m m'' -∗  hash_tape3 α (ns) γ2 γ3 -∗ ⌜m''!!α=Some (n::ns)⌝
                                      ={⊤∖↑N.@"hash"}=∗ R (<[v:=n]> m) ∗ P (<[v:=n]> m) (<[α:=ns]> m'') ∗
                                      hash_auth3 (<[v:=n]> m) γ1 γ2 γ4 γ5∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns, Q2 res ns
                                )
      }}}
}.


Section test.
  Variables val_size:nat.
  Variables max_hash_size:nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.
  Context `{conerisGS Σ, !con_hash3 val_size max_hash_size max_hash_size_pos}.
  Definition hash_tape3' α ns γ2 γ3 γ5:= (hash_tape3 α ns γ2 γ3 ∗ [∗ list] n∈ns, hash_set_frag3 n γ2 γ5)%I.
                                                    

  Lemma con_hash_presample_test N f l hm γ1 γ2 γ3 γ4 γ5 γlock γ_token E ns α :
    ↑N⊆E ->
    con_hash_inv3 N f l hm (λ _ _, True) (λ _, True )γ1 γ2 γ3 γ4 γ5 γ_token γlock -∗
    hash_tape3' α ns γ2 γ3 γ5-∗
    ↯ (amortized_error val_size max_hash_size max_hash_size_pos) -∗
    hash_token3 1 γ_token -∗
    state_update E E (∃ (n:fin (S val_size)),
          hash_tape3' α (ns++[fin_to_nat n]) γ2 γ3 γ5 
      ).
  Proof.
    iIntros (Hsubset) "#Hinv [Ht Hfrag] Herr Htoken".
    iMod (con_hash_presample3 _ _ _ _ _ _ _ _ _ _ _ _ _
            (λ m m' m'', (∃ n : fin (S val_size), hash_tape3 α (ns ++ [fin_to_nat n]) γ2 γ3 ∗
                                                    hash_set_frag3 (fin_to_nat n) _ _))%I with "[//][-Hfrag]") as "Hcont".
    - by apply nclose_subseteq'. 
    - iIntros (???) "Hauth".
      iMod (hash_tape_presample with "[//][$][$][$][$]") as "(%&$&$&$)".
      + repeat apply subseteq_difference_r; last by apply nclose_subseteq'.
        all: by apply ndot_ne_disjoint.
      + apply subseteq_difference_r; last by apply nclose_subseteq'.
        by apply ndot_ne_disjoint.
      + done.
    - iFrame. iDestruct "Hcont" as "(%&%&%&%&$&$)". by iModIntro.
  Qed.
  
    
  Lemma con_hash_spec_test3 N f l hm γ1 γ2 γ3 γ4 γ5 γ_token γlock α n ns (v:nat):
    {{{ con_hash_inv3 N f l hm (λ _ _, True) (λ _, True )γ1 γ2 γ3 γ4 γ5 γ_token  γlock ∗ hash_tape3' α (n::ns) γ2 γ3 γ5 }}}
      f #v α
      {{{ (res:nat), RET (#res);  hash_frag3 v res γ1 γ2 γ4 ∗
                                (hash_tape3' α ns γ2 γ3 γ5 ∗ ⌜res=n⌝ ∨
                                 hash_tape3' α (n::ns) γ2 γ3 γ5
                                )
      }}}.
  Proof.
    iIntros (Φ) "[#Hinv [Ht Hlis]] HΦ".
    iApply (con_hash_spec3 _ _ _ _ _ _ _ _ _ _ _ _ _ (λ res, hash_frag3 v res γ1 γ2 γ4 ∗ hash_tape3 _ _ _ _ ∗ [∗ list] n0 ∈ (n :: ns), hash_set_frag3 n0 γ2 γ5 )%I (λ n' ns', ⌜n=n'⌝ ∗ ⌜ns = ns'⌝ ∗ hash_frag3 v n γ1 γ2 γ4 ∗ hash_tape3 _ _ _ _ ∗ [∗ list] n0 ∈ (ns), hash_set_frag3 n0 γ2 γ5)%I with "[$Hinv Ht Hlis]").
    - iIntros (??) "_ _ Htauth Hauth".
      case_match.
      + iDestruct (hash_auth_duplicate with "[$]") as "#$"; first done. by iFrame.
      + iDestruct (hash_tape_auth_frag_agree with "[$][$]") as "%".
        iDestruct "Hlis" as "[H1 Hlis]".
        iMod (hash_auth_insert with "[$][$]") as "H"; first done.
        iDestruct (hash_auth_duplicate with "[$]") as "#$"; first by rewrite lookup_insert.
        iFrame. iModIntro. iIntros. rewrite insert_id; last done. iFrame. iIntros. iFrame. done. 
    - iNext. iIntros (res) "[(?&?&?)|(%&->&->&?&?)]".
      + iApply "HΦ". iFrame. iRight. iFrame.
      + iApply "HΦ". simplify_eq. iFrame. iLeft. by iFrame.
  Qed.

  Lemma con_hash_spec_hashed_before3 N f l hm γ1 γ2 γ3 γ4 γ5 γtoken γlock α ns res (v:nat):
    {{{ con_hash_inv3 N f l hm (λ _ _, True) (λ _, True) γ1 γ2 γ3 γ4 γ5 γtoken γlock ∗ hash_tape3' α ns γ2 γ3 γ5 ∗ hash_frag3 v res γ1 γ2 γ4}}}
      f #v α
      {{{ RET (#res);  hash_frag3 v res γ1 γ2 γ4 ∗
                       (hash_tape3' α ns γ2 γ3 γ5)
      }}}.
  Proof. 
    iIntros (Φ) "(#Hinv & [Ht ?] & #Hf) HΦ".
    iApply (con_hash_spec3 _ _ _ _ _ _ _ _ _ _ _ _ _(λ res' , ⌜res=res'⌝ ∗ hash_tape3 _ _ _ _ ∗hash_frag3 v res γ1 γ2 γ4  )%I (λ _ _, ⌜False⌝)%I with "[$Hinv Ht]").
    - iIntros (??) "_ _ Htauth Hauth".
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
