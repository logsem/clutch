From clutch.coneris Require Import coneris hash_view_interface.

Set Default Proof Using "Type*".

(** * TODO *)
(** * For the hash with lock, the lock protects the hash table plus the authoritative part of the maps*)

Definition tape_m_elements (tape_m : gmap val (list nat)) :=
    concat (map_to_list tape_m).*2.

Class seq_hash `{!conerisGS Σ} {h:hash_view} `{!hvG Σ} (val_size:nat):= Seq_Hash
{
  (** * Operations *)
  init_hash : val;
  (* incr_counter : val; *)
  allocate_tape : val;
  compute_hash : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  seq_hashG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  seq_hash_tape_gname: Type;
  
  (** * Predicates *)
  abstract_seq_hash {L : seq_hashG Σ} (f: val) (m:gmap nat nat) (tape_m : gmap val (list nat)) (γ1:seq_hash_tape_gname) (γ2: hv_name): iProp Σ;
  concrete_seq_hash {L:seq_hashG Σ} (f:val) (m:gmap nat nat) : iProp Σ; 
  seq_hash_tape {L : seq_hashG Σ} (α:val) (ns:list nat) (γ: seq_hash_tape_gname) : iProp Σ;
  (** * General properties of the predicates *)
  #[global] abstract_seq_hash_timeless {L : seq_hashG Σ} f m tape_m γ1 γ2 ::
    Timeless (abstract_seq_hash (L:=L) f m tape_m γ1 γ2);
  #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m ::
    Timeless (concrete_seq_hash (L:=L) f m);
  #[global] seq_hash_tape_timeless {L : seq_hashG Σ} α ns γ ::
    Timeless (seq_hash_tape (L:=L) α ns γ);

  seq_hash_presample {L : seq_hashG Σ} f m tape_m γ1 γ2 α E (ε:nonnegreal) ns:
    abstract_seq_hash (L:=L) f m tape_m γ1 γ2 -∗
    seq_hash_tape (L:=L) α ns γ1 -∗
    ↯ (nnreal_div (nnreal_nat (length (map_to_list m) + length (tape_m_elements tape_m))) (nnreal_nat(val_size+1))) -∗
    ↯ ε -∗
    state_update E E (∃ (n:nat),
          ↯ ((nnreal_div (nnreal_nat(val_size+1)) (nnreal_nat (S val_size - (length (map_to_list m) + length (tape_m_elements tape_m))))) *ε) ∗
          seq_hash_tape (L:=L) α ns γ1 ∗
          abstract_seq_hash (L:=L) f m tape_m γ1 γ2)
}.

