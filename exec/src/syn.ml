(* The extracted probblaze syntax, re-exported with its constructors.
   [Probblaze] (the extracted module) also defines modules [Z], [String],
   [Nat], … that would shadow the OCaml standard library if opened. *)

module P = Probblaze

type z = Z.t

type binder = P.binder = BAnon | BNamed of string
type mode = P.mode = OS | MS
type handler_semantics = P.handler_semantics = Deep | Shallow
type eff_val = P.eff_val = EffName of string | EffLabel of z

type base_lit = P.base_lit =
  | LitUnit
  | LitInt of z
  | LitBool of bool
  | LitLoc of z
  | LitLbl of z

type un_op = P.un_op = NegOp | MinusUnOp

type bin_op = P.bin_op =
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp
  | AndOp | OrOp | XorOp
  | ShiftLOp | ShiftROp
  | LeOp | LtOp | EqOp
  | OffsetOp

type expr = P.expr =
  | Val of value
  | Var of string
  | Rec of binder * binder * expr
  | App of expr * expr
  | UnOp of un_op * expr
  | BinOp of bin_op * expr * expr
  | If of expr * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | InjL of expr
  | InjR of expr
  | Case of expr * expr * expr
  | AllocN of expr * expr
  | Load of expr
  | Store of expr * expr
  | AllocTape of expr
  | Rand of expr * expr
  | Effect of string * expr
  | Do of eff_val * expr
  | Handle of handler_semantics * mode * eff_val * expr * expr * expr

and value = P.val0 =
  | LitV of base_lit
  | RecV of binder * binder * expr
  | KontV of frame list
  | ContV of z * frame list
  | PairV of value * value
  | InjLV of value
  | InjRV of value

and frame = P.frame =
  | AppLCtx of value
  | AppRCtx of expr
  | UnOpCtx of un_op
  | BinOpLCtx of bin_op * value
  | BinOpRCtx of bin_op * expr
  | IfCtx of expr * expr
  | PairLCtx of value
  | PairRCtx of expr
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx of expr * expr
  | AllocNLCtx of value
  | AllocNRCtx of expr
  | LoadCtx
  | StoreLCtx of value
  | StoreRCtx of expr
  | AllocTapeCtx
  | RandLCtx of value
  | RandRCtx of expr
  | DoCtx of z
  | HandleCtx of handler_semantics * mode * z * expr * expr

let unit_v = LitV LitUnit
let int_v n = LitV (LitInt (Z.of_int n))
let bool_v b = LitV (LitBool b)

(* [App f a] for curried applications of values. *)
let app_v f args = List.fold_left (fun e a -> App (e, Val a)) (Val f) args
