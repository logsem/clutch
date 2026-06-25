(* Contains various functions *)

let rec pow m n =
  if n = 0 then 1
  else if n mod 2 = 0 then pow (m * m) (n / 2)
  else m * pow (m * m) ((n - 1) / 2)

let abs_f x =
  if x<0. then -.x else x

let string_to_int s =
  let l = String.length s in
  let res = ref 0 in
  for i = 0 to l - 1 do
    res := !res + (Char.(code s.[l - 1 - i] - code '0') * pow 10 i)
  done;
  !res

let int_to_string i =
  if i = 0 then "0"
  else (
  let rec aux i s =
    if i = 0 then s
    else aux (i/10) (String.make 1 Char.(chr (i mod 10 + code '0')) ^ s)
  in aux i ""
 )

let aff_flst l =
  List.iter (fun x -> Printf.printf "%f|" x) l;
  Printf.printf "\n"

let aff_l_op l =
  List.fold_left
    (fun _ y ->
      match y with
      | None -> Printf.printf "⊥\n"
      | Some n -> Printf.printf "%d\n" n)
    () l
