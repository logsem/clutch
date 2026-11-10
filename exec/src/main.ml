(* probblaze-exec: run, trace and test the probblaze case studies. *)
open Cmdliner
open Syn

let ( let* ) = Result.bind

(* ------------------------------------------------------------------------ *)
(* Common options                                                           *)

let p_arg = Arg.(value & opt int 7 & info [ "p"; "prime" ] ~docv:"P" ~doc:"The prime of the toy group.")

let kind_conv = Arg.enum [ ("zpx", Instances.Zpx); ("qr", Instances.Qr) ]

let group_arg =
  Arg.(value & opt kind_conv Instances.Zpx & info [ "g"; "group" ] ~docv:"KIND"
         ~doc:"$(b,zpx): the units modulo the prime (order p-1); $(b,qr): the squares modulo a safe prime (prime order (p-1)/2).")

let group_t = Term.(const (fun k p -> (k, p)) $ group_arg $ p_arg)
let make_group (k, p) = Instances.make k p
let seed_arg = Arg.(value & opt int 0 & info [ "seed" ] ~docv:"S" ~doc:"Seed of the random choices.")

let run_arg =
  Arg.(value & opt int 0 & info [ "run" ] ~docv:"J"
         ~doc:"Index of the run: run $(docv) of seed $(b,--seed) is the $(docv)-th run that $(b,dist) and $(b,adv) sample.")

let choices_arg =
  Arg.(value & opt (some (list int)) None & info [ "choices" ] ~docv:"I,J,..."
         ~doc:"Outcomes of the samplings, in order; once they run out, the seeded strategy continues.")

let max_steps_arg =
  Arg.(value & opt int 5_000_000 & info [ "max-steps" ] ~docv:"N" ~doc:"Step budget per run.")

let max_leaves_arg =
  Arg.(value & opt int 200_000 & info [ "max-leaves" ] ~docv:"N"
         ~doc:"Enumerate at most $(docv) runs; beyond that, sample.  0 always samples.")

let samples_arg = Arg.(value & opt int 10_000 & info [ "samples" ] ~docv:"N" ~doc:"Number of sampled runs.")

let confidence_arg =
  Arg.(value & opt float 0.99 & info [ "confidence" ] ~docv:"C"
         ~doc:"Confidence level of the intervals (0.9, 0.95, 0.99 or 0.999).")

let validate_arg =
  Arg.(value & flag & info [ "validate" ]
         ~doc:"Check every step against the extracted reference decomposition ($(b,decomp)/$(b,fill)).  Slow.")

let options_arg =
  Arg.(value & flag & info [ "options" ] ~doc:"Print $(b,inl ()) as NONE and $(b,inr v) as SOME v.")

let case_pos i = Arg.(required & pos i (some string) None & info [] ~docv:"CASE")
let env_pos i = Arg.(required & pos i (some string) None & info [] ~docv:"ENV")
let sys_pos i name = Arg.(required & pos i (some string) None & info [] ~docv:name)

let settings max_steps max_leaves samples seed confidence validate =
  { Analysis.max_steps; max_leaves; samples; seed; confidence; validate }

let settings_t =
  Term.(const settings $ max_steps_arg $ max_leaves_arg $ samples_arg $ seed_arg $ confidence_arg $ validate_arg)

let guard f = try f () with Failure m | Invalid_argument m -> Error (`Msg m)

let header c g lines =
  Printf.printf "# %s — %s\n# %s\n" c.Scenarios.name c.doc (Instances.describe g);
  List.iter (Printf.printf "# %s\n") lines

(* ------------------------------------------------------------------------ *)
(* list                                                                     *)

let list_cmd =
  let go () =
    List.iter
      (fun (c : Scenarios.case) ->
        Printf.printf "%s — %s\n  systems:\n" c.name c.doc;
        List.iter (fun (s : Scenarios.sys) -> Printf.printf "    %-16s %s\n" s.s_name s.s_doc) c.systems;
        Printf.printf "  environments:\n";
        List.iter (fun (e : Scenarios.env) -> Printf.printf "    %-16s %s\n" e.e_name e.e_doc) c.envs;
        Printf.printf "  claims:\n";
        List.iter
          (function
            | Scenarios.Always { w; expect; doc } -> Printf.printf "    %s %s always returns %s: %s\n" w.env w.sys expect doc
            | Adv_zero { env; x; y; doc } -> Printf.printf "    adv(%s, %s, %s) = 0: %s\n" env x y doc
            | Adv_le { lhs = e, x, y; rhs = e', x', y'; doc } ->
                Printf.printf "    adv(%s, %s, %s) ≤ adv(%s, %s, %s): %s\n" e x y e' x' y' doc
            | Adv_bound { env; x; y; bound = b, _; doc } -> Printf.printf "    adv(%s, %s, %s) ≤ %s: %s\n" env x y b doc)
          c.claims;
        Printf.printf "  checked by default on: %s\n"
          (String.concat ", " (List.map (fun (k, p) -> Printf.sprintf "%s %d" (Instances.kind_name k) p) c.instances));
        print_newline ())
      Scenarios.cases;
    Ok ()
  in
  Cmd.v (Cmd.info "list" ~doc:"List the case studies, their systems, environments and claims.") Term.(term_result (const go $ const ()))

(* ------------------------------------------------------------------------ *)
(* run                                                                      *)

type format = Text | Json | Mermaid

let format_arg =
  Arg.(value & opt (enum [ ("text", Text); ("json", Json); ("mermaid", Mermaid) ]) Text
       & info [ "format" ] ~docv:"FMT" ~doc:"Trace format: $(b,text), $(b,json) or $(b,mermaid).")

type level = L_none | L_view | L_proto | L_exec

let level_conv = Arg.enum [ ("none", L_none); ("view", L_view); ("proto", L_proto); ("exec", L_exec) ]

let level_doc =
  "$(b,view): the environment's observations; $(b,proto): also effects, resumptions and samples; \
   $(b,exec): every step and heap access; $(b,none)."

let level_arg = Arg.(value & opt level_conv L_proto & info [ "trace" ] ~docv:"LEVEL" ~doc:level_doc)

let strategy seed run choices =
  let fallback = Explore.seeded ~seed ~run in
  match choices with None -> fallback | Some l -> Explore.replay l fallback

let collect level =
  let events = ref [] in
  let lvl = match level with L_exec -> Trace.Exec | L_view -> Trace.View | _ -> Trace.Proto in
  let emit n ev = if Trace.in_level lvl ev then events := (n, ev) :: !events in
  ((if level = L_none then None else Some emit), fun () -> List.rev !events)

let choices_string ch = String.concat "," (List.map (fun (i, _) -> string_of_int i) ch)

let run_cmd =
  let go case env sys p seed run choices level format max_steps validate options =
    guard @@ fun () ->
    Pp.options := options;
    let c = Scenarios.find_case case in
    let g = make_group p in
    let emit, events = collect level in
    let r =
      Explore.run ?emit ~validate ~max_steps ~strategy:(strategy seed run choices)
        (Analysis.world c g ~env ~sys)
    in
    let evs = events () in
    (match format with
    | Text ->
        header c g [ Printf.sprintf "%s applied to %s" env sys ];
        List.iter (fun e -> print_endline (Trace.text_line e)) evs;
        Printf.printf "# result: %s after %d steps\n" (Explore.result_key r.result) r.final.steps;
        Printf.printf "# choices: %s\n" (if r.choices = [] then "(none)" else choices_string r.choices)
    | Json ->
        let j =
          `Assoc
            [ ("case", `String case); ("env", `String env); ("system", `String sys);
              ("result", `String (Explore.result_key r.result)); ("steps", `Int r.final.steps);
              ("group", `String (Instances.describe g));
              ("choices", `List (List.map (fun (i, n) -> `Assoc [ ("outcome", `Int i); ("range", `String (Z.to_string n)) ]) r.choices));
              ("events", `List (List.map Trace.json_event evs)) ]
        in
        print_endline (Yojson.Safe.pretty_to_string j)
    | Mermaid -> print_string (Trace.mermaid evs));
    Ok ()
  in
  let doc = "Run an environment against a system once and print its trace." in
  Cmd.v (Cmd.info "run" ~doc)
    Term.(term_result
            (const go $ case_pos 0 $ env_pos 1 $ sys_pos 2 "SYS" $ group_t $ seed_arg $ run_arg $ choices_arg $ level_arg
           $ format_arg $ max_steps_arg $ validate_arg $ options_arg))

(* ------------------------------------------------------------------------ *)
(* dist, adv                                                                *)

let dist_cmd =
  let go case env sys p s options =
    guard @@ fun () ->
    Pp.options := options;
    let c = Scenarios.find_case case in
    let g = make_group p in
    header c g [ Printf.sprintf "output distribution of %s applied to %s" env sys ];
    print_endline (Analysis.describe_estimate (Analysis.estimate s c g ~env ~sys));
    Ok ()
  in
  Cmd.v (Cmd.info "dist" ~doc:"The output distribution of an environment against a system.")
    Term.(term_result (const go $ case_pos 0 $ env_pos 1 $ sys_pos 2 "SYS" $ group_t $ settings_t $ options_arg))

let adv_cmd =
  let go case env x y p s =
    guard @@ fun () ->
    let c = Scenarios.find_case case in
    let g = make_group p in
    header c g [ Printf.sprintf "advantage of %s in telling %s from %s, on output true" env x y ];
    let a = Analysis.estimate s c g ~env ~sys:x and b = Analysis.estimate s c g ~env ~sys:y in
    Printf.printf "%s:\n%s\n%s:\n%s\n" x (Analysis.describe_estimate a) y (Analysis.describe_estimate b);
    Printf.printf "advantage: %s\n" (Analysis.adv_to_string (Analysis.adv s a b));
    Ok ()
  in
  Cmd.v (Cmd.info "adv" ~doc:"The advantage |Pr[env X = true] - Pr[env Y = true]|.")
    Term.(term_result (const go $ case_pos 0 $ env_pos 1 $ sys_pos 2 "X" $ sys_pos 3 "Y" $ group_t $ settings_t))

(* ------------------------------------------------------------------------ *)
(* diff                                                                     *)

let diff_cmd =
  let go case env x y p seed run choices max_steps options level =
    guard @@ fun () ->
    Pp.options := options;
    let c = Scenarios.find_case case in
    let g = make_group p in
    let trace sys =
      let emit, events = collect level in
      let r =
        Explore.run ?emit ~max_steps ~strategy:(strategy seed run choices) (Analysis.world c g ~env ~sys)
      in
      (r, List.map Trace.plain_line (events ()))
    in
    let rx, tx = trace x in
    (* The second world replays the outcomes of the first. *)
    let choices' = Some (List.map fst rx.choices) in
    let ry, ty =
      let emit, events = collect level in
      let r =
        Explore.run ?emit ~max_steps ~strategy:(strategy seed run choices') (Analysis.world c g ~env ~sys:y)
      in
      (r, List.map Trace.plain_line (events ()))
    in
    header c g
      [ Printf.sprintf "traces of %s applied to %s (-) and to %s (+), on the same sampling outcomes" env x y ];
    List.iter print_endline (Trace.diff tx ty);
    Printf.printf "# %s: %s, choices %s\n# %s: %s, choices %s\n" x (Explore.result_key rx.result)
      (choices_string rx.choices) y (Explore.result_key ry.result) (choices_string ry.choices);
    Ok ()
  in
  Cmd.v (Cmd.info "diff" ~doc:"Diff the protocol traces of two systems under the same sampling outcomes.")
    Term.(term_result
            (const go $ case_pos 0 $ env_pos 1 $ sys_pos 2 "X" $ sys_pos 3 "Y" $ group_t $ seed_arg $ run_arg $ choices_arg
           $ max_steps_arg $ options_arg
           $ Arg.(value & opt level_conv L_proto & info [ "trace" ] ~docv:"LEVEL" ~doc:level_doc)))

(* ------------------------------------------------------------------------ *)
(* check                                                                    *)

let check_claim s c g claim =
  let est env sys = Analysis.estimate_cached s c g ~env ~sys in
  match claim with
  | Scenarios.Always { w; expect; doc } -> (
      let e = est w.env w.sys in
      let what = Printf.sprintf "%s %s always returns %s (%s)" w.env w.sys expect doc in
      match e with
      | Exact (d, st) ->
          let ok = List.for_all (fun (k, _) -> k = expect) d in
          ( ok,
            Printf.sprintf "%s: exact over %d runs%s" what st.leaves
              (if ok then ""
               else "; outcomes: " ^ String.concat ", " (List.map (fun (k, (_, q)) -> k ^ " " ^ Stats.q_to_string q) d)) )
      | Sampled cn ->
          let ok = List.for_all (fun (k, _) -> k = expect) cn.by_key in
          ( ok,
            Printf.sprintf "%s: %d sampled runs%s" what cn.n
              (if ok then ""
               else "; outcomes: " ^ String.concat ", " (List.map (fun (k, (_, n)) -> Printf.sprintf "%s %d" k n) cn.by_key)) ))
  | Adv_zero { env; x; y; doc } ->
      let a = est env x and b = est env y in
      let nb = Analysis.non_boolean a @ Analysis.non_boolean b in
      let adv = Analysis.adv s a b in
      let ok = nb = [] && match adv with Adv_exact q -> Q.equal q Q.zero | Adv_sampled (_, (lo, _)) -> lo <= 0. in
      ( ok,
        Printf.sprintf "adv(%s, %s, %s) = %s (%s)%s" env x y (Analysis.adv_to_string adv) doc
          (if nb = [] then "" else "; non-boolean outcomes: " ^ String.concat ", " nb) )
  | Adv_le { lhs = e, x, y; rhs = e', x', y'; doc } ->
      let l = Analysis.adv s (est e x) (est e y) and r = Analysis.adv s (est e' x') (est e' y') in
      let ok =
        match (l, r) with
        | Adv_exact l, Adv_exact r -> Q.leq l r
        | _ -> fst (Analysis.adv_bounds l) <= snd (Analysis.adv_bounds r)
      in
      ( ok,
        Printf.sprintf "adv(%s, %s, %s) = %s  ≤  adv(%s, %s, %s) = %s (%s)" e x y (Analysis.adv_to_string l) e' x' y'
          (Analysis.adv_to_string r) doc )
  | Adv_bound { env; x; y; bound = name, b; doc } ->
      let a = est env x and b' = est env y in
      let nb = Analysis.non_boolean a @ Analysis.non_boolean b' in
      let l = Analysis.adv s a b' and bound = b g in
      let ok = nb = [] && match l with Adv_exact l -> Q.leq l bound | _ -> fst (Analysis.adv_bounds l) <= Q.to_float bound in
      ( ok,
        Printf.sprintf "adv(%s, %s, %s) = %s  ≤  %s = %s (%s)%s" env x y (Analysis.adv_to_string l) name
          (Stats.q_to_string bound) doc
          (if nb = [] then "" else "; non-boolean outcomes: " ^ String.concat ", " nb) )

let check_cmd =
  let go cases kind ps s =
    guard @@ fun () ->
    let cases = if cases = [] then Scenarios.cases else List.map Scenarios.find_case cases in
    let fails = ref 0 and total = ref 0 in
    List.iter
      (fun (c : Scenarios.case) ->
        let instances =
          match ps with
          | None -> c.instances
          | Some ps -> List.map (fun p -> (Option.value kind ~default:Instances.Zpx, p)) ps
        in
        List.iter
          (fun (k, p) ->
            let g = Instances.make k p in
            Printf.printf "== %s, %s\n%!" c.name (Instances.describe g);
            List.iter
              (fun claim ->
                incr total;
                let ok, line = check_claim s c g claim in
                if not ok then incr fails;
                Printf.printf "  [%s] %s\n%!" (if ok then "ok" else "FAIL") line)
              c.claims)
          instances)
      cases;
    Printf.printf "%d/%d claims hold%s\n" (!total - !fails) !total
      (if !fails = 0 then "" else Printf.sprintf "; %d FAIL" !fails);
    if !fails = 0 then Ok () else Error (`Msg "some claims failed")
  in
  let cases_arg = Arg.(value & pos_all string [] & info [] ~docv:"CASE") in
  let kind_arg =
    Arg.(value & opt (some kind_conv) None & info [ "g"; "group" ] ~docv:"KIND" ~doc:"Group kind for $(b,--prime).")
  in
  let ps_arg =
    Arg.(value & opt (some (list int)) None & info [ "p"; "prime" ] ~docv:"P,..."
           ~doc:"Primes of the toy groups; by default each case study uses its own list (see $(b,list)).")
  in
  Cmd.v
    (Cmd.info "check"
       ~doc:"Test the registered claims: exactly by enumeration when the runs fit the budget, statistically otherwise.")
    Term.(term_result (const go $ cases_arg $ kind_arg $ ps_arg $ settings_t))

let () =
  let doc = "execute, trace and statistically test the probblaze case studies" in
  exit (Cmd.eval (Cmd.group (Cmd.info "probblaze-exec" ~doc) [ list_cmd; run_cmd; dist_cmd; adv_cmd; diff_cmd; check_cmd ]))
