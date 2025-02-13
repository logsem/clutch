From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris abstract_tape hocap_rand_alt lib.map lock
  hash_view_interface con_hash_interface4.

Set Default Proof Using "Type*".


Section con_hash_impl.
  Variable val_size max_key : nat.
  Context `{Hc: conerisGS Σ,
              (* h : @hash_view Σ Hc, Hhv: hvG Σ, *)
                lo:lock, Hl: lockG Σ,
                  (* r: @rand_spec Σ Hc, Hr: randG Σ, *)
                    Hm: inG Σ (excl_authR (gmapO nat natO)),
                      Ht: !abstract_tapesGS Σ,
                        Hr: !rand_spec' val_size,
                  h : @hash_view Σ Hc, Hhv: hvG Σ
    }.


  Definition alloc_tapes : val :=
    (rec: "alloc_tapes" "tm" "n" :=
       if: ("n" - #1) < #0 then
         #()
       else
        let: "α" := rand_allocate_tape #() in
         set "tm" ("n" - #1) "α";;
        "alloc_tapes" "tm" ("n" - #1)).

  Definition init_hash_state : val :=
   λ: "max_val",
      let: "val_map" := init_map #() in
      let: "tape_map" := init_map #() in
      alloc_tapes "tape_map" ("max_key" + #1);;
      ("val_map", "tape_map").

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we look up the tape for this value
     flip a bit with that tape, and save it in the map *)

  Definition compute_hash : val :=
    λ: "vm" "tm" "v",
      match: get "vm" "v" with
      | SOME "b" => "b"
      | NONE =>
          match: get "tm" "v" with
            | SOME "α" =>
                let: "b" := rand_tape "α" in
                set "vm" "v" "b";;
                "b"
          | NONE => #0
          end
      end.


  Definition compute_con_hash :val:=
    λ: "lhm" "v",
      let, ("l", "hm", "tm") := "lhm" in
      acquire "l";;
      let: "output" := compute_hash "hm" "tm" "v" in
      release "l";;
      "output".


  Definition compute_con_hash_specialized (lhm:val):val:=
    λ: "v",
      let, ("l", "hm", "tm") := lhm in
      acquire "l";;
      let: "output" := compute_hash "hm" "tm" "v" in
      release "l";;
      "output".


  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "max_val",
      let, ("hm", "tm") := init_hash_state "max_val" in
      let: "l" := newlock #() in
      compute_hash ("l", "hm", "tm").

  Definition hash_key_tape (tm : gmap nat (val * list nat)) γ:=
    ([∗ map] k ↦ t ∈ tm,
      rand_tapes t.1 t.2 γ.1 ∗
        t.1 ◯↪N ( val_size ; t.2 ) @ γ.2)%I.

  Definition hash_key_tape_auth (tm :  gmap nat val) (tcont : gmap val (list nat)) γ :=
     (([∗ map] k ↦ α ∈ tm, rand_token α γ.1) ∗
        ● ((λ t, (val_size, t))<$>tcont) @ γ.2)%I.


  Definition abstract_con_hash (f:val) (l:val) (hm:val) γ_hv γ_tapes : iProp Σ :=
    ∃ m tm tcont,
      ⌜f=compute_con_hash_specialized (l, hm)%V⌝ ∗
           own γ_hv (●E m) ∗
           hash_key_tape_auth tm tcont γ_tapes
      (* hv_auth (L:=Hhv) m γ1 ∗ *)
  .

  Definition abstract_con_hash_inv N f l hm γ_hv γ_tapes :=
    (inv (N.@"hash") (abstract_con_hash f l hm γ_hv γ_tapes))%I.


  Definition concrete_con_hash (hm:val) (m : gmap nat nat) R {HR: ∀ m, Timeless (R m)} γ_hv : iProp Σ :=
    ∃ (lvm ltm : loc) (vm: gmap nat nat) (tm: gmap nat loc),
      ⌜ hm=#lvm ⌝ ∗
      map_list lvm ((λ n, LitV (LitInt (Z.of_nat n))) <$> vm) ∗
      map_list ltm ((λ a, LitV (LitLbl a)) <$> tm) ∗
      ([∗ map] i ↦ α ∈ tm,
        (∃ v, ⌜ m !! i = Some v ⌝ ∗ ⌜ vm !! i = Some v ⌝) ∨
        (∃ v vs, ⌜ m !! i = Some v ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪N (val_size ; (v::vs))) ∨
        (⌜ m !! i = None ⌝ ∗ ⌜ vm !! i = None ⌝ ∗ α ↪N (val_size ; nil))) ∗
      own γ_hv (◯E m) ∗
      R m.



  Definition concrete_con_hash_inv hm l R {HR: ∀ m, Timeless (R m )} γ_hv γ_lock :=
    is_lock (L:=Hl) γ_lock l (∃ m, concrete_con_hash hm m R γ_hv).
  

  Definition hash_auth m γ1:=
    (hv_auth (L:=Hhv) m γ1 )%I.

  Definition hash_frag k v γ1 :=
    (hv_frag (L:=Hhv) k v γ1)%I.

