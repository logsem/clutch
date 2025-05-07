From clutch Require Import eris.
From clutch.eris.lib Require Import list.


(* 
For Karger's algorithm (https://en.wikipedia.org/wiki/Karger's_algorithm): 2 solutions

Either do specific things, or use an union find structure

*)




Section graph_code.
  #[local] Open Scope expr_scope.
  Definition empty_graph : expr := list_nil.

  Definition add_edge : val :=
    λ: "src" "dst" "g", list_cons ("src", "dst") "g".
  
  Definition remove_edge : val :=
    rec: "remove_edge" "src" "dst" "g" :=
      if: "g" = empty_graph 
      then empty_graph
      else
        let: "h" := list_head "g" in
        let: "curr_src" := Fst "h" in
        let: "curr_dst" := Snd "h" in
        let: "new_g" := list_tail "g" in
        if: ("curr_src" = "src") || ("curr_dst" = "dst")
        then "new_g"
        else 
          let: "new_g" := "remove_edge" "src" "dst" "new_g" in
          add_edge "curr_src" "curr_dst" "new_g"
  .

  Definition get_output_nodes : val :=
    λ: "src" "g",
      list_map 
        (λ: "p", Snd "p") 
        (list_filter (λ: "p", Fst "p" = "src") "g")
  .

  Definition get_input_nodes : val :=
    λ: "dst" "g",
      list_map 
        (λ: "p", Fst "p") 
        (list_filter (λ: "p", Snd "p" = "dst") "g")
  .

  Definition get_edges : val := λ: "g", "g".

  Definition get_nodes : val :=
    rec: "get_nodes" "g" :=
      let: "nodes" := "get_nodes" (list_tail "g") in
      let: "h" := list_head "g" in
      let: "n1" := Fst "h" in
      let: "n2" := Snd "h" in
      let: "new_nodes" := 
        if: list_mem "n1" "nodes" 
        then "g" 
        else list_cons "n1" "nodes"
      in
      if: list_mem "n2" "new_nodes" 
      then "g" 
      else list_cons "n2" "new_nodes"
  .

End graph_code.


Section karger.
  Definition karger : val :=
    λ: "g",
    let: "pick_random_edge" := "todo" in
    let: "go" := 
      rec: "g" "nodes" "assoc" := 
        let: "size" := list_length "nodes" in 
        if: "size" = #2 
        then "assoc"
        else 
          let: "p" := "pick_random_edge" "g" in
          let: "e" := Fst "p" in
          let: "g" := Snd "p" in
          let: "assoc" := "todo" in
          "todo"
    in 
    "".
End karger.