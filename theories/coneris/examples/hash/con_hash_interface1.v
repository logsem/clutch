From clutch.coneris Require Import coneris .

Set Default Proof Using "Type*".

Class con_hash1 `{!conerisGS Σ} (val_size:nat):= Con_Hash1
{
  (** * Operations *)
  init_hash1 : val;
  (* incr_counter : val; *)
  allocate_tape1 : val;
  compute_hash1 : val;
  (** * Ghost state *)
  
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  
  hash_view_gname:Type;
  hash_set_gname:Type;
  hash_lock_gname:Type;
  
  (** * Predicates *)
  con_hash_inv1 (f l hm: val) (γ1:hash_view_gname) (γ3: hash_set_gname) (γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape1 (α:val) (ns:list nat) (γ3: hash_set_gname): iProp Σ;
  con_hash_view1 (v res:nat) (γ:hash_view_gname) (γ3 : hash_set_gname): iProp Σ;
  hash_set1 (s: gset nat) (γ3:hash_set_gname) : iProp Σ; 
  
  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_tape_timeless α ns γ3::
    Timeless (hash_tape1 α ns γ3 ); 
  #[global] con_hash_view_timeless v res γ γ3::
    Timeless (con_hash_view1 v res γ γ3);
  #[global] hash_set_timeless s γ3 ::
    Timeless (hash_set1 s γ3);
  #[global] con_hash_inv_persistent f l hm γ1 γ3 γ_lock ::
    Persistent (con_hash_inv1 f l hm γ1 γ3 γ_lock);
  #[global] con_hash_view_persistent v res γ γ3::
    Persistent (con_hash_view1 v res γ γ3);
  con_hash_view_frag_frag_agree k v1 v2 γ γ3:
    con_hash_view1 k v1 γ γ3 -∗ con_hash_view1 k v2 γ γ3-∗ ⌜v1=v2⌝; 
  con_hash_view_in_hash_set γ1 γ3 s v res:
    con_hash_view1 v res γ1 γ3 -∗ hash_set1 s γ3 -∗ ⌜res ∈ s⌝ ;
  hash_tape_in_hash_set α ns γ s:
    hash_tape1 α ns γ -∗ hash_set1 s γ -∗ ⌜Forall (λ x, x∈s) ns⌝;
  hash_tape_valid α ns γ3:
    hash_tape1 α ns γ3-∗ ⌜Forall (λ x, x<=val_size)%nat ns⌝;

  (** need to update *)
  con_hash_presample1 γ3 E (ε εI εO:nonnegreal) ns α s :
    (εI * (size s) + εO * (val_size + 1 - size s) <= ε * (val_size + 1))%R ->
    hash_tape1 α ns γ3 -∗
    ↯ ε -∗
    hash_set1 s γ3 -∗
    state_update E E (∃ (n:fin (S val_size)),
          hash_tape1 α (ns++[fin_to_nat n]) γ3 ∗
          ( (⌜fin_to_nat n ∈ s⌝) ∗ hash_set1 s γ3 ∗ ↯ εI ∨
            (⌜fin_to_nat n ∉ s⌝) ∗ hash_set1 (s∪{[(fin_to_nat n)]}) γ3 ∗ ↯ εO
          )
      );

  con_hash_init1:
    {{{ True }}}
      init_hash1 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ3 γ_lock, con_hash_inv1 f l hm γ1 γ3 γ_lock ∗
                                                  hash_set1 ∅ γ3
      }}};

  con_hash_alloc_tape1 f l hm γ1 γ3 γ_lock:
    {{{ con_hash_inv1 f l hm γ1 γ3 γ_lock }}}
      allocate_tape1 #()
      {{{ (α: val), RET α; hash_tape1 α [] γ3 }}};
  
  con_hash_spec1 f l hm γ1 γ3 γlock α n ns (v:nat):
    {{{ con_hash_inv1 f l hm γ1 γ3 γlock ∗ hash_tape1 α (n::ns) γ3 }}}
      f #v α
      {{{ (res:nat), RET (#res);  con_hash_view1 v res γ1 γ3 ∗
                                (hash_tape1 α ns γ3 ∗ ⌜res=n⌝ ∨
                                 hash_tape1 α (n::ns) γ3
                                )
      }}};
  
  con_hash_spec_hashed_before1 f l hm γ1 γ3 γlock α ns res (v:nat):
    {{{ con_hash_inv1 f l hm γ1 γ3 γlock ∗ hash_tape1 α ns γ3 ∗ con_hash_view1 v res γ1 γ3 }}}
      f #v α
      {{{ RET (#res);  con_hash_view1 v res γ1 γ3 ∗
                       (hash_tape1 α ns γ3 )
      }}}
}.

