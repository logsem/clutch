From clutch.coneris Require Import coneris .

Set Default Proof Using "Type*".


Class con_hash0 `{!conerisGS Σ} (val_size:nat):= Con_Hash0
{
  (** * Operations *)
  init_hash0 : val;
  allocate_tape0 : val;
  compute_hash0 : val;
  (** * Ghost state *)
  
  (** [name] is used to associate [locked] with [is_lock] *)
  hash_tape_gname: Type;
  hash_lock_gname:Type;
  
  (** * Predicates *)
  con_hash_inv0 (N:namespace) (f l hm: val) (R:gmap nat nat -> iProp Σ) {HR: ∀ m, Timeless (R m )} (γ:hash_tape_gname) (γ_lock:hash_lock_gname): iProp Σ;
  hash_tape0 (α:val) (ns:list nat) (γ:hash_tape_gname): iProp Σ;
  
  (** * General properties of the predicates *)
  #[global] hash_tape_timeless α ns γ::
    Timeless (hash_tape0 α ns γ); 
  #[global] con_hash_inv_persistent N f l hm R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock ::
    Persistent (con_hash_inv0 N f l hm R γ_tape γ_lock); 
  
  hash_tape_valid α ns γ:
    hash_tape0 α ns γ-∗ ⌜Forall (λ x, x<=val_size)%nat ns⌝;
  hash_tape_exclusive α ns ns' γ:
    hash_tape0 α ns γ-∗ hash_tape0 α ns' γ-∗ False;
  hash_tape_presample N γ γ_lock f l hm R {HR: ∀ m, Timeless (R m )} α ns ε ε2 E:
  ↑(N)⊆E ->
    (∀ x : fin (S val_size), (0 <= ε2 x)%R)->
    (SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε)%R ->
    con_hash_inv0 N f l hm R γ γ_lock -∗
    hash_tape0 α ns γ -∗ ↯ ε -∗
    state_update E E (∃ n, 
          ↯ (ε2 n) ∗
          hash_tape0 α (ns++[fin_to_nat n]) γ); 

  con_hash_init0 N R {HR: ∀ m, Timeless (R m )} :
    {{{ R ∅}}}
      init_hash0 #()
      {{{ (f:val), RET f; ∃ l hm γ_tape γ_lock, con_hash_inv0 N f l hm R γ_tape γ_lock }}}; 

  con_hash_alloc_tape0 N f l hm R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock:
  {{{ con_hash_inv0 N f l hm R γ_tape γ_lock
  }}}
      allocate_tape0 #()
      {{{ (α: val), RET α; hash_tape0 α [] γ_tape }}}; 
  
  con_hash_spec0 N f l hm R {HR: ∀ m, Timeless (R m )} γ_tape γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv0 N f l hm R γ_tape γ_lock ∗ 
      ( ∀ m , R m -∗ state_update (⊤) (⊤)
             match m!!v with
             | Some res => R m ∗ Q1 res
             | None => ∃ n ns, hash_tape0 α (n::ns) γ_tape ∗ 
                              (hash_tape0 α (ns) γ_tape ={⊤}=∗ R (<[v:=n]> m) ∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns, Q2 res ns
                                )
      }}};

}.
