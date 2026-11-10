(* Descriptors of finite value types, in place of mathcomp's [finType]
   structures, for the realisers of [fin_val_type.card], [prod_fvt] and
   [vg_fvt] in [extract.v]. *)

type desc = Atom of Z.t  (* the integers 0..n-1, or a group of order n *) | Prod of desc * desc

let rec card = function Atom n -> n | Prod (a, b) -> Z.mul (card a) (card b)
