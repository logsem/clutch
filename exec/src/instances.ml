(* Toy instances of the case studies' class parameters.

   The group is Zpˣ for a prime p ([valgroup_Zpx]): elements are the
   integers 1..p-1, the operations are the extracted programs, the
   generator is the least primitive root, and [n''] is p-3, so that the
   protocols sample exponents from [0, p-2], i.e. uniformly modulo the
   order p-1. *)
open Syn
module P = Probblaze

let is_prime p =
  p >= 2
  &&
  let rec go d = d * d > p || (p mod d <> 0 && go (d + 1)) in
  go 2

let prime_factors n =
  let rec go n d acc =
    if n = 1 then List.rev acc
    else if d * d > n then List.rev (if List.mem n acc then acc else n :: acc)
    else if n mod d = 0 then go (n / d) d (if List.mem d acc then acc else d :: acc)
    else go n (d + 1) acc
  in
  go n 2 []

let primitive_root p =
  let q = p - 1 in
  let fs = prime_factors q in
  let zp = Z.of_int p in
  let ok g = List.for_all (fun f -> not (Z.equal (Z.powm (Z.of_int g) (Z.of_int (q / f)) zp) Z.one)) fs in
  let rec find g = if g >= p then invalid_arg "primitive_root" else if ok g then g else find (g + 1) in
  find 2

type kind = Zpx | Qr

(* Elements of the carrier are represented by their integer value.  The
   [finType] field is not used by the programs, except through the
   realiser of [vg_fvt] ([exec/extract/extract.v]), which reads the order
   from it. *)
let group_record order =
  { P.vgG = Obj.magic (Exec_fin.Atom (Z.of_int order)); vgval = (fun x -> LitV (LitInt (Obj.obj x))) }

type group = {
  kind : kind;
  p : int;
  order : int;
  root : int;  (* the generator *)
  vg : P.val_group;
  cg : P.clutch_group_struct;
  vgg : P.val_group_generator;
}

let zpx p =
  if p < 3 || not (is_prime p) then invalid_arg (Printf.sprintf "--prime %d: need a prime ≥ 3" p);
  let p3 = Z.of_int (p - 3) in
  let root = primitive_root p in
  let vg = group_record (p - 1) in
  let cg =
    {
      P.vunit = P.vunit_z;
      vinv = P.vinv_z p3;
      vmult = P.vmult_p p3;
      veq = P.veq_p;
      int_of_vg = P.int_of_vg_p;
      vg_of_int = P.vg_of_int_p p3;
      _UU03c4_G = P.TInt;
    }
  in
  let vgg = { P.g = Obj.repr (Z.of_int root); n'' = p3 } in
  { kind = Zpx; p; order = p - 1; root; vg; cg; vgg }

(* The squares modulo a safe prime p = 2q + 1, of prime order q, generated
   by 4 ([exec/theories/qr_ops.v]). *)
let qr p =
  if p < 5 || not (is_prime p) || not (is_prime ((p - 1) / 2)) then
    invalid_arg (Printf.sprintf "--group qr --prime %d: need a safe prime p = 2q + 1 ≥ 5 (5, 7, 11, 23, 47, 59, 83, …)" p);
  let q = (p - 1) / 2 in
  let p3 = Z.of_int (p - 3) and zq = Z.of_int q and gen = Z.of_int 4 in
  let g = zpx p in
  let cg = { g.cg with P.int_of_vg = P.qr_int_of_vg p3 zq gen; vg_of_int = P.qr_vg_of_int p3 zq gen } in
  let vgg = { P.g = Obj.repr gen; n'' = Z.of_int (q - 2) } in
  { kind = Qr; p; order = q; root = 4; vg = group_record q; cg; vgg }

let make kind p = match kind with Zpx -> zpx p | Qr -> qr p

let kind_name = function Zpx -> "zpx" | Qr -> "qr"

let describe g =
  match g.kind with
  | Zpx ->
      Printf.sprintf "Zpˣ with p = %d (order %d, generator %d; exponents sampled from 0..%d)" g.p g.order g.root
        (g.order - 1)
  | Qr ->
      Printf.sprintf "squares mod %d (prime order %d, generator %d; exponents sampled from 0..%d)" g.p g.order
        g.root (g.order - 1)

(* The integers 0..n-1 as a finite value type ([exec/theories/fin_ops.v]). *)
let fin_type n = { P.fvT = Obj.magic (Exec_fin.Atom (Z.of_int n)); fvtval = (fun x -> LitV (LitInt (Obj.obj x))) }

let fin_struct n = { P.int_of_fvt = P.fin_int_of; fvt_of_int = P.fin_of_int (Z.of_int n); _UU03c4_FT = P.TInt }
