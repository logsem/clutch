From mathcomp Require Import all_ssreflect ssrnat zmodp.

From stdpp Require fin.

Set Default Proof Using "Type*".

Section zmodp_fin.

  Context {n : nat}.
  Local Notation "'p'" := (S (S n)).

  Definition ord_of_fin (c : Fin.t p) : 'Z_p :=
    (Ordinal (n:=(Zp_trunc p).+2)
       (m:=fin.fin_to_nat c)
       ((introT leP (fin.fin_to_nat_lt c)))).

  Definition fin_of_ord (c : 'Z_p) : Fin.t p :=
    @Fin.of_nat_lt (nat_of_ord c) p (elimTF leP (ltn_ord c)).

  Fact fin_of_ord_of_fin x : fin_of_ord (ord_of_fin x) = x.
  Proof. unfold fin_of_ord, ord_of_fin. apply fin.fin_to_nat_inj.
         by rewrite fin.nat_to_fin_to_nat. Qed.

  Fact ord_of_fin_of_ord (x : 'Z_p) : ord_of_fin (fin_of_ord x) = x.
  Proof. unfold fin_of_ord, ord_of_fin. apply ord_inj.
         by rewrite /nat_of_ord fin.fin_to_nat_to_fin. Qed.

End zmodp_fin.
