(* A case study of coupon collection *)
From clutch Require Export clutch.
From clutch.lib Require Export map.

Set Default Proof Using "Type*".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition couponN := nroot.@"coupon".

  Definition check_map_helper : expr :=
    (rec: "check_helper" "m" "k" "n" :=
       if: "k" = "n"
       then #true
       else if: get "m" "k" = #1 then "check_helper" "m" ("k"+#1) else #false                
    ).

  Definition check_map : expr:=
    λ: "m" "n",
      check_map_helper "m" #0 "n".
      
  Definition coupon_helper : expr :=
    rec: "coupon_helper" "m" "n" "cnt" :=
      if: check_map "m" "n" then #() else
        "cnt" <- !"cnt" + #1;;
        let: "k" := rand "n" from #() in
        set "m" "k" #1;;
        "coupon_helper" "m" "n" "cnt".
        
  Definition coupon_collection : expr :=
    λ: "n",
      let: "m" := init_map in
      set "m" "n" #();;
      let: "cnt" := ref #0 in
      coupon_helper "m" "n" "cnt";;
      !"cnt".

  
  
End proofs.
