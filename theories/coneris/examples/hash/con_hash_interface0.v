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
  
  hash_view_gname:Type;
  hash_map_gname:Type;
  hash_lock_gname:Type;
  
  (** * Predicates *)
  con_hash_inv0  (f l hm: val) (γ1:hash_view_gname) (γ2:hash_map_gname) (γ_lock:hash_lock_gname): iProp Σ;
  (* concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ;  *)
  hash_tape0 (α:val) (ns:list nat) : iProp Σ;
  con_hash_view0 (v res:nat) (γ:hash_view_gname): iProp Σ;
  
  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_tape_timeless α ns ::
    Timeless (hash_tape0 α ns); 
  #[global] con_hash_view_timeless v res γ ::
    Timeless (con_hash_view0 v res γ);
  #[global] con_hash_inv_persistent f l hm γ1 γ2 γ_lock ::
   Persistent (con_hash_inv0 f l hm γ1 γ2 γ_lock);
  con_hash_view_frag_frag_agree k v1 v2 γ :
    con_hash_view0 k v1 γ -∗ con_hash_view0 k v2 γ -∗ ⌜v1=v2⌝; 

  con_hash_presample0 E (ε:nonnegreal) ns α (ε2 : fin (S val_size) → R) :
    (∀ x : fin (S val_size), (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    hash_tape0 α ns -∗
    ↯ ε -∗
    state_update E E (∃ n,
          ↯ (ε2 n) ∗
          hash_tape0 α (ns++[fin_to_nat n]) 
      );

  con_hash_init0:
    {{{ True }}}
      init_hash0 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ_lock, con_hash_inv0 f l hm γ1 γ2 γ_lock }}};

  con_hash_alloc_tape0:
    {{{ True }}}
      allocate_tape0 #()
      {{{ (α: val), RET α; hash_tape0 α [] }}};
  
  con_hash_spec0 f l hm γ1 γ2 γlock α n ns (v:nat):
    {{{ con_hash_inv0 f l hm γ1 γ2 γlock ∗ hash_tape0 α (n::ns) }}}
      f #v α
      {{{ (res:nat), RET (#res);  con_hash_view0 v res γ1 ∗
                                (hash_tape0 α ns ∗ ⌜res=n⌝ ∨
                                 hash_tape0 α (n::ns)
                                )
      }}};
  con_hash_spec_hashed_before0 f l hm γ1 γ2 γlock α ns res (v:nat):
    {{{ con_hash_inv0 f l hm γ1 γ2 γlock ∗ hash_tape0 α ns ∗ con_hash_view0 v res γ1}}}
      f #v α
      {{{ RET (#res);  con_hash_view0 v res γ1 ∗
                       (hash_tape0 α ns)
      }}}
}.

