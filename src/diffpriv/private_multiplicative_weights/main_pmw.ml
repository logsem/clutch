#use "private_multiplicative_weights.ml"
let () = Random.self_init ()

let path = "data/"
let file = "state.csv"
(* let file = "adult_with_pii_sanitized_short.csv" *)

let path_gif = "gif/data/"
let file_gif = "gif"

let () =
  let file = match List.find_index (fun x -> x = "--file") (Array.to_list Sys.argv) with
    | Some i -> Sys.argv.(i+1)
    | None -> "rd_data.csv"
  in
  if (Array.mem "--list" Sys.argv) then (
    let size, index, db = mk_histo_l (path ^ file) in
    let log_card_q = List.length index in
    let nb_q = 1_000 * log_card_q in
    let stream_query =
      let a = ref nb_q in
      fun bs ->
        if !a <= 0 then None
        else (
          a := !a - 1;
          Some
            (get_rd_query_l index))
    in
    let res, db', nb_upd, c, t =
      oPMW_l
        size
        db
        index
        (get_unif_l index size)
        stream_query
        (float_of_int log_card_q)
        1 1 1 100 1 100
        ~gif:(if (Array.mem "--gif" Sys.argv) then Some (path_gif ^ file_gif) else None)
    in
    if (Array.mem "--gif" Sys.argv) then (
      let writer = open_out (path_gif ^ "len.csv") in
      Printf.fprintf writer "%d\n" nb_upd;
      close_out writer
    );
    Printf.(
      printf "c: %d\nt: %d\n" c t;
      printf "- NB UPDATE : %d\n- ORIGINAL DB :\n" nb_upd;
      aff_db_l db index;
      printf "\n\n- SANITIZED DB :\n";
      aff_db_l db' index;
      printf "\n\n- UNIF DB :\n";
      aff_db_l (get_unif_l index size) index;
      printf "\n\n- LIST RESULT :\n";
      printf "%d\n" (max_l2 res);
      printf "size init : %d | size fin : %d\n" (sum_l db) (sum_l db');
      ()
    )
  )
  else (
    let size, domaine, db = mk_histo (path ^ file) in
    (* Printf.printf "tl: %d\n" (pow 2 (List.length domaine)); *)
    (* let card_q = pow 2 (List.length domaine) in *)
    (* let nb_q = 2 * card_q in *)
    let log_card_q = List.length domaine in
    let nb_q = 10000 * log_card_q in
    let stream_query =
      let a = ref nb_q in
      fun bs ->
        if !a <= 0 then None
        else (
          a := !a - 1;
          Some
            (get_rd_query domaine))
    in
    let res, db', nb_upd, c, t =
      oPMW
        size
        domaine
        db
        (get_unif domaine)
        stream_query
        (float_of_int log_card_q)
        1 1 0.01 0.01
        ~gif:(if (Array.mem "--gif" Sys.argv) then Some (path_gif ^ file_gif) else None)
    in
    if (Array.mem "--gif" Sys.argv) then (
      let writer = open_out (path_gif ^ "len.csv") in
      Printf.fprintf writer "%d\n" nb_upd;
      close_out writer
    );
    Printf.(
      printf "c: %f\nt: %f\n" c t;
      printf "- NB UPDATE : %d\n- ORIGINAL DB :\n" nb_upd;
      aff_db db;
      printf "\n\n- SANITIZED DB :\n";
      aff_db db';
      printf "\n\n- LIST RESULT :\n";
      printf "%f\n" (max_l res);
      printf "Above 0.1: %f (%d/%d)\n" ( float_of_int (count_above res 0.1) /. float_of_int nb_q) (count_above res 0.1) nb_q;
      printf "Above 0.01: %f (%d/%d)\n" ( float_of_int (count_above res 0.01) /. float_of_int nb_q) (count_above res 0.01) nb_q
    )
  )
