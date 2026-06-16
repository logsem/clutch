let sample_i distrib =
  (* -- This sampling funcion is not a good sampling function. *)
  (*    It would be if there was a uniform sampling method on [0,1] *)
  (*    which is not possible since the uniform distribution on [0,1] does not exists + float issues *)
  (*    Then this function is juste for illustration purpose *)
  let a = Random.float 1. in
  let sum = ref 0. in
  let res = ref (-1) in
  for i = 0 to List.length distrib - 1 do
    if !res = -1 && !sum >= a then res := i
    else sum := !sum +. List.nth distrib i
  done;
  !res

(* -- In this example, our databases set will be {0,1}^k *)
(*    We wont store the whole set, instead we build a function that for some i gives back a dataset *)

let get_db k i =
  let ui = ref i in
  List.init k (fun i ->
      let res = float_of_int (!ui mod 2) in
      ui := !ui / 2;
      res)

let query_s f distrib = f get_db sample_i distrib

let count lst =
  List.fold_left (fun x y -> x +. y) 0. lst /. float_of_int (List.length lst)

let count_between b e lst =
  let res = ref 0. in
  List.iteri (fun i x -> if b <= i && i < e then res := !res +. x) lst;
  !res

let aff_lst_inf lst =
  List.iter (fun x -> Printf.printf "%d|" (int_of_float x)) lst;
  Printf.printf "\n"

let aff_lst_flo lst =
  List.iter (Printf.printf "%f|") lst;
  Printf.printf "\n"

let distrib_unif n = List.init n (fun _ -> 1. /. float_of_int n)
let distrib_dirac i n = List.init n (fun j -> if i = j then 1. else 0.)

let normailze_lst lst =
  let sum = List.fold_left (fun x y -> x +. y) 0. lst in
  List.map (fun x -> x /. sum) lst

let distrib_rd n = normailze_lst (List.init n (fun _ -> Random.float 100.))
