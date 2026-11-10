(* Compact printing of values, expressions and frames. *)
open Syn

(* Print [inl ()] as NONE and [inr v] as SOME v. *)
let options = ref false

let zs = Z.to_string

let binder = function BAnon -> "_" | BNamed x -> x

let lam f x =
  match f with
  | BAnon -> Printf.sprintf "λ%s" (binder x)
  | BNamed f -> Printf.sprintf "rec %s %s" f (binder x)

let rec value ?(depth = 6) v =
  if depth <= 0 then "…"
  else
    let d = depth - 1 in
    match v with
    | LitV LitUnit -> "()"
    | LitV (LitInt n) -> zs n
    | LitV (LitBool b) -> string_of_bool b
    | LitV (LitLoc l) -> "ℓ" ^ zs l
    | LitV (LitLbl l) -> "ι" ^ zs l
    | RecV (f, x, _) -> "⟨" ^ lam f x ^ "⟩"
    | KontV k -> Printf.sprintf "kont[%d]" (List.length k)
    | ContV (r, k) -> Printf.sprintf "cont@ℓ%s[%d]" (zs r) (List.length k)
    | PairV _ -> "(" ^ String.concat ", " (List.map (value ~depth:d) (tuple v)) ^ ")"
    | InjLV (LitV LitUnit) when !options -> "NONE"
    | InjRV w when !options -> "SOME " ^ atom ~depth:d w
    | InjLV w -> "inl " ^ atom ~depth:d w
    | InjRV w -> "inr " ^ atom ~depth:d w

(* Left-nested pairs [((a, b), c)] are how [(a, b, c)] is written. *)
and tuple = function
  | PairV ((PairV _ as l), r) -> tuple l @ [ r ]
  | PairV (l, r) -> [ l; r ]
  | v -> [ v ]

and atom ?(depth = 6) v =
  match v with
  | InjLV _ | InjRV _ -> (
      match v with
      | InjLV (LitV LitUnit) when !options -> value ~depth v
      | _ -> "(" ^ value ~depth v ^ ")")
  | _ -> value ~depth v

let un_op = function NegOp -> "~" | MinusUnOp -> "-"

let bin_op = function
  | PlusOp -> "+" | MinusOp -> "-" | MultOp -> "*" | QuotOp -> "quot"
  | RemOp -> "rem" | AndOp -> "&" | OrOp -> "|" | XorOp -> "^^"
  | ShiftLOp -> "<<" | ShiftROp -> ">>" | LeOp -> "≤" | LtOp -> "<"
  | EqOp -> "=" | OffsetOp -> "+ₗ"

let eff_val names = function
  | EffName s -> s
  | EffLabel l -> names l

(* [names l] renders an effect label, e.g. ["send#3"]. *)
let rec expr ?(names = fun l -> "#" ^ zs l) ?(depth = 4) e =
  if depth <= 0 then "…"
  else
    let d = depth - 1 in
    let ex = expr ~names ~depth:d in
    match e with
    | Val v -> value ~depth:(depth + 1) v
    | Var x -> x
    | Rec (f, x, _) -> lam f x ^ ".…"
    | App (a, b) -> Printf.sprintf "%s %s" (ex a) (paren names d b)
    | UnOp (op, a) -> un_op op ^ paren names d a
    | BinOp (op, a, b) -> Printf.sprintf "%s %s %s" (paren names d a) (bin_op op) (paren names d b)
    | If (c, _, _) -> Printf.sprintf "if %s then … else …" (ex c)
    | Pair (a, b) -> Printf.sprintf "(%s, %s)" (ex a) (ex b)
    | Fst a -> "fst " ^ paren names d a
    | Snd a -> "snd " ^ paren names d a
    | InjL a -> "inl " ^ paren names d a
    | InjR a -> "inr " ^ paren names d a
    | Case (a, _, _) -> Printf.sprintf "match %s with …" (ex a)
    | AllocN (n, v) -> Printf.sprintf "alloc[%s] %s" (ex n) (paren names d v)
    | Load a -> "!" ^ paren names d a
    | Store (a, b) -> Printf.sprintf "%s <- %s" (ex a) (ex b)
    | AllocTape a -> "tape " ^ paren names d a
    | Rand (a, b) -> Printf.sprintf "rand(%s) %s" (ex b) (paren names d a)
    | Effect (s, _) -> Printf.sprintf "effect %s in …" s
    | Do (n, a) -> Printf.sprintf "do %s %s" (eff_val names n) (paren names d a)
    | Handle (_, _, n, a, _, _) -> Printf.sprintf "handle[%s] %s" (eff_val names n) (ex a)

and paren names depth e =
  match e with
  | Val _ | Var _ | Pair _ -> expr ~names ~depth e
  | _ -> "(" ^ expr ~names ~depth e ^ ")"
