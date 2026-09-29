#use "numeric_sparse_vector.ml"
(* #use "db_query.ml" *)

(* Hashtbl. implementation *)
let mw x f v eta =
  let r = Hashtbl.copy f in
  if v >= c_query f x then Hashtbl.iter (fun a b -> Hashtbl.replace r a (1. -. b)) r;
  Hashtbl.iter (fun a b -> Hashtbl.replace r a ((exp ((-.eta) *. b)) *. (Hashtbl.find x a))) r;
  norm r;
  r

let oPMW ?(gif=None) size domaine db unif stream_q log_card_q num den alpha beta =
  write_db db gif 0;
  let c = 4. *. (log (float_of_int (List.length domaine))) /.  (alpha *. alpha) in
  (* let t = 0.000005 *. (float_of_int size) *. ((float_of_int den) *. 18. *. c *. (log (2.) +. log_card_q +. log (4. *. c) -. log beta)) /. ((float_of_int num) *. (float_of_int size)) in *)
  let t = ((float_of_int den) *. 18. *. c *. (log (2.) +. log_card_q +. log (4. *. c) -. log beta)) /. ((float_of_int num) *. (float_of_int size)) in
  let f = num_sparse_vector num den (int_of_float t) (int_of_float c) db in
  let rec aux i bs distrib =
    match stream_q bs with
    | None -> (bs, distrib, i, c, t) (* no more queries we stop *)
    | Some q -> (
        if i >= int_of_float c then (* we retrun only from the distribution *)
          aux i ((abs_f (c_query q db -. c_query q distrib)) :: bs) distrib
        else (
          (match f (fun x' -> int_of_float ((float_of_int size) *. (c_query q x' -. c_query q distrib))) with
          | None -> ( match f (fun x' -> int_of_float ((float_of_int size) *. (c_query q distrib -. c_query q x'))) with
              | None -> aux i ((abs_f (1. -. c_query q db /. c_query q distrib)) :: bs) distrib
              | Some v -> (
                  write_db distrib gif (i +1) ;
                  let a = c_query q distrib -. float_of_int v /. (float_of_int size) in
                  aux (i + 1) ((abs_f (1. -. c_query q db /. a)) :: bs) (mw distrib q a  (alpha /. 2.))))
          | Some v -> (
              write_db distrib gif (i +1) ;
              let a = c_query q distrib +. float_of_int v /. (float_of_int size) in
              aux (i + 1) ((abs_f (1.-. c_query q db /. a)) :: bs) (mw distrib q a  (alpha /. 2.)))
          )
        )
    )
  in
  aux 0 [] unif

(* List implementation *)
let mw_l db size q v etanum etaden =
  if c_query_l q db < v
  then normalize_l (List.mapi (fun i x -> int_of_float(exp (-. ((float_of_int etanum) /. (float_of_int etaden)) *. (if List.nth q i then 0. else 1.)) *. (float_of_int x))) db) size
  else normalize_l (List.mapi (fun i x -> int_of_float(exp (-. ((float_of_int etanum) /. (float_of_int etaden)) *. (if List.nth q i then 1. else 0.)) *. (float_of_int x))) db) size

let oPMW_large gif size db index unif stream_q log_card_q enum eden anum aden bnum bden c t upd f1 f2=
  write_db_l index db gif 0;
  let f = num_sparse_vector enum eden t c db in
  let rec aux i bs distrib =
    match stream_q bs with
    | None -> (bs, distrib, i, c, t) (* no more queries we stop *)
    | Some q -> (
        if i >= c then (* we retrun only from the distribution *)
          aux i ((abs (c_query_l q db - c_query_l q distrib)) :: bs) distrib
        else (
          (match f (f1 q distrib) with
          | None -> (match f (f2 q distrib) with
              | None -> aux i ((abs (c_query_l q db - c_query_l q distrib)) :: bs) distrib
              | Some v -> (
                  write_db_l index distrib gif (i +1) ;
                  let a = c_query_l q distrib - v in
                  aux (i + 1) ((abs (c_query_l q db - a)) :: bs) (upd distrib size q a  (anum) (2*aden) )))
          | Some v -> (
              write_db_l index distrib gif (i +1) ;
              let a = c_query_l q distrib + v in
              aux (i + 1) ((abs (c_query_l q db - a)) :: bs) (upd distrib size q a  (anum) (2*aden)))
          )
        )
    )
  in
  aux 0 [] unif

let oPMW_l ?(gif=None) size db index unif stream_q log_card_q enum eden anum aden bnum bden =
  write_db_l index db gif 0;
  let c = int_of_float (4. *. (log (float_of_int (List.length db))) *. (float_of_int aden *. float_of_int aden) /.  (float_of_int anum *. float_of_int anum)) in
  let t = int_of_float (1. *. ((float_of_int eden) *. 18. *. (float_of_int c) *. (log (2.) +. log_card_q +. log (4. *. (float_of_int c)) -. log (float_of_int bnum)) +. log (float_of_int bden)) /. ((float_of_int enum) *. (float_of_int size))) in
  let f1 = (fun q distrib x' -> c_query_l q x' - c_query_l q distrib) in
  let f2 = (fun q distrib x' -> c_query_l q distrib - c_query_l q x') in
  oPMW_large gif size db index unif stream_q log_card_q enum eden anum aden bnum bden c t (mw_l) (f1) f2
