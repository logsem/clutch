From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

(** An interface of a simple hash view*)

(* A hash function is collision free if the partial map it
     implements is an injective function *)
(* Definition coll_free (m : gmap nat nat) := *)
(*   forall k1 k2, *)
(*   is_Some (m !! k1) -> *)
(*   is_Some (m !! k2) -> *)
(*   m !!! k1 = m !!! k2 -> *)
(*   k1 = k2. *)

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
  (* hv_auth_coll_free {L:hvG Σ} m γ: hv_auth (L:=L) m γ -∗ ⌜coll_free m⌝; *)
  hv_auth_duplicate_frag {L:hvG Σ} m n b γ:
    m!!n=Some b -> hv_auth (L:=L) m γ ==∗ hv_auth (L:=L) m γ ∗ hv_frag (L:=L) n b γ;
  hv_auth_frag_agree {L:hvG Σ} m γ k v:
    hv_auth (L:=L) m γ  ∗ hv_frag (L:=L) k v γ -∗
    ⌜m!!k=Some v⌝;
  hv_auth_insert {L:hvG Σ} m n x γ:
    m!!n=None ->
    hv_auth (L:=L) m γ ==∗
    hv_auth (L:=L) (<[n:=x]> m) γ ∗ hv_frag (L:=L) n x γ             
}.
