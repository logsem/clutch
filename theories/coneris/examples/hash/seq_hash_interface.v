From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

(** * TODO *)
(** * For the hash with lock, the lock protects the hash table plus the authoritative part of the maps*)

(* A hash function is collision free if the partial map it
     implements is an injective function *)
Definition coll_free (m : gmap nat nat) :=
  forall k1 k2,
  is_Some (m !! k1) ->
  is_Some (m !! k2) ->
  m !!! k1 = m !!! k2 ->
  k1 = k2.

Class hash_view `{!conerisGS Σ} := Hash_View
{
  hvG : gFunctors -> Type;
  hv_name : Type; 
  hv_auth {L:hvG Σ} : gmap nat nat ->  hv_name -> iProp Σ;
  hv_frag {L:hvG Σ} : nat -> nat -> hv_name -> iProp Σ;

  hv_auth_timeless {L:hvG Σ} m γ::
  Timeless (hv_auth (L:=L) m γ);
  hv_frag_timeless {L:hvG Σ} k v γ::
  Timeless (hv_frag (L:=L) k v γ);
  hv_frag_persistent {L:hvG Σ} k v γ::
  Persistent (hv_frag (L:=L) k v γ);
  
  hv_auth_init {L:hvG Σ}:
  (⊢|==> (∃ γ, hv_auth (L:=L) ∅ γ))%I;
  hv_auth_coll_free {L:hvG Σ} m γ: hv_auth (L:=L) m γ -∗ ⌜coll_free m⌝;
  hv_auth_duplicate_frag {L:hvG Σ} m n b γ:
    m!!n=Some b -> hv_auth (L:=L) m γ ==∗ hv_auth (L:=L) m γ ∗ hv_frag (L:=L) n b γ;
  hv_auth_frag_agree {L:hvG Σ} m γ k v:
    hv_auth (L:=L) m γ  ∗ hv_frag (L:=L) k v γ -∗
    ⌜m!!k=Some v⌝;
  hv_auth_insert {L:hvG Σ} m n x γ:
    m!!n=None ->
    Forall (λ m : nat, x ≠ m) (map (λ p : nat * nat, p.2) (map_to_list m)) ->
    hv_auth (L:=L) m γ ==∗
    hv_auth (L:=L) (<[n:=x]> m) γ ∗ hv_frag (L:=L) n x γ             
}.

Class seq_hash `{!conerisGS Σ} (val_size:nat):= Seq_Hash
{
  (** * Operations *)
  new_counter : val;
  (* incr_counter : val; *)
  allocate_tape : val;
  incr_counter_tape : val;
  read_counter : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  counterG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  counter_name: Type;
  (** * Predicates *)
  is_counter {L : counterG Σ} (N:namespace) (counter: val) (γ: counter_name): iProp Σ;
  (* counter_tapes_auth {L : counterG Σ} (γ: tape_name) (m:gmap loc (list nat)): iProp Σ; *)
  counter_tapes {L : counterG Σ} (α:val) (ns:list nat): iProp Σ;
  counter_content_auth {L : counterG Σ} (γ: counter_name) (z:nat): iProp Σ;
  counter_content_frag {L : counterG Σ} (γ: counter_name) (f:frac) (z:nat): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_counter_persistent {L : counterG Σ} N c γ1 ::
    Persistent (is_counter (L:=L) N c γ1);
  (* #[global] counter_tapes_auth_timeless {L : counterG Σ} γ m :: *)
  (*   Timeless (counter_tapes_auth (L:=L) γ m); *)
  #[global] counter_tapes_timeless {L : counterG Σ} α ns ::
    Timeless (counter_tapes (L:=L) α ns);
  #[global] counter_content_auth_timeless {L : counterG Σ} γ z ::
    Timeless (counter_content_auth (L:=L) γ z);
  #[global] counter_content_frag_timeless {L : counterG Σ} γ f z ::
    Timeless (counter_content_frag (L:=L) γ f z);
  
  (* counter_tapes_auth_exclusive {L : counterG Σ} γ m m': *)
  (* counter_tapes_auth (L:=L) γ m -∗ counter_tapes_auth (L:=L) γ m' -∗ False; *)
  counter_tapes_exclusive {L : counterG Σ} α ns ns':
  counter_tapes (L:=L) α ns -∗ counter_tapes (L:=L) α ns' -∗ False;
  (* counter_tapes_agree {L : counterG Σ} γ α m ns: *)
  (* counter_tapes_auth (L:=L) γ m -∗ counter_tapes (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝; *)
  counter_tapes_valid {L : counterG Σ} α ns:
    counter_tapes (L:=L) α ns -∗ ⌜Forall (λ n, n<=3)%nat ns⌝;
  (* counter_tapes_update {L : counterG Σ} γ α m ns ns': *)
  (*   Forall (λ x, x<=3%nat) ns'-> *)
  (*   counter_tapes_auth (L:=L) γ m -∗ counter_tapes (L:=L) γ α ns ==∗ *)
  (*   counter_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ counter_tapes (L:=L) γ α (ns'); *)
  counter_tapes_presample {L:counterG Σ} N E γ c α ns ε (ε2 : fin 4%nat -> R):
  ↑N ⊆ E ->
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ->
  is_counter(L:=L) N c γ  -∗
  counter_tapes (L:=L) α (ns) -∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ counter_tapes (L:=L) α (ns ++ [fin_to_nat n]));

  counter_content_auth_exclusive {L : counterG Σ} γ z1 z2:
    counter_content_auth (L:=L) γ z1 -∗ counter_content_auth (L:=L) γ z2 -∗ False;
  counter_content_less_than {L : counterG Σ} γ z z' f:
  counter_content_auth (L:=L) γ z -∗ counter_content_frag (L:=L) γ f z' -∗ ⌜(z'<=z)%nat ⌝;
  counter_content_frag_combine {L:counterG Σ} γ f f' z z':
    (counter_content_frag (L:=L) γ f z ∗ counter_content_frag (L:=L) γ f' z')%I ≡
    counter_content_frag (L:=L) γ (f+f')%Qp (z+z')%nat;
  counter_content_agree {L : counterG Σ} γ z z':
    counter_content_auth (L:=L) γ z -∗ counter_content_frag (L:=L) γ 1%Qp z' -∗ ⌜(z'=z)%nat ⌝;
  counter_content_update {L : counterG Σ} γ f z1 z2 z3:
    counter_content_auth (L:=L) γ z1 -∗ counter_content_frag (L:=L) γ f z2 ==∗
    counter_content_auth (L:=L) γ (z1+z3)%nat ∗ counter_content_frag (L:=L) γ f (z2+z3)%nat;
  
  (** * Program specs *)
  new_counter_spec {L : counterG Σ} E N:
  {{{ True }}} new_counter #() @E
    {{{ c, RET c; ∃ γ1, is_counter (L:=L) N c γ1 ∗
                           counter_content_frag (L:=L) γ1 1%Qp 0%nat
    }}};
  allocate_tape_spec {L: counterG Σ} N E c γ1 :
    ↑N ⊆ E->
    {{{ is_counter (L:=L) N c γ1 }}}
      allocate_tape #() @ E
      {{{ (v:val), RET v; counter_tapes (L:=L) v []
      }}};
  incr_counter_tape_spec_some {L: counterG Σ} N E c γ1 (Q:nat->iProp Σ) (α:val) n ns:
    ↑N⊆E ->
    {{{ is_counter (L:=L) N c γ1 ∗
        counter_tapes (L:=L) α (n::ns) ∗
        (  ∀ (z:nat), counter_content_auth (L:=L) γ1 z ={E∖↑N}=∗
                    counter_content_auth (L:=L) γ1 (z+n) ∗ Q z)
           
    }}}
      incr_counter_tape c α @ E
                                 {{{ (z:nat), RET (#z, #n); counter_tapes (L:=L) α ns ∗
                                                          Q z }}}; 
  read_counter_spec {L: counterG Σ} N E c γ1 Q:
    ↑N ⊆ E ->
    {{{  is_counter (L:=L) N c γ1 ∗
         (∀ (z:nat), counter_content_auth (L:=L) γ1 z ={E∖↑N}=∗
                    counter_content_auth (L:=L) γ1 z∗ Q z)
        
    }}}
      read_counter c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}
}.

