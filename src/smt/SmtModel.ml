open Collections
open Syntax
open Solution
open SmtLang
open SmtUtils
open SmtExprEncodings

(** Emits the code that evaluates the model returned by Z3. *)
let eval_model (symbolics: Syntax.ty_or_exp VarMap.t)
    (num_nodes: Integer.t)
    (eassert: Syntax.exp option)
    (renaming: string StringMap.t) : command list =
  let var x = "Var:" ^ x in
  (* Compute eval statements for labels *)
  (* let labels = *)
  (*   AdjGraph.fold_vertices (fun u acc -> *)
  (*       let lblu = label_var u in *)
  (*       let tm = mk_var (StringMap.find_default lblu lblu renaming) |> mk_term in *)
  (*       let ev = mk_eval tm |> mk_command in *)
  (*       let ec = mk_echo ("\"" ^ (var lblu) ^ "\"") |> mk_command in *)
  (*       ec :: ev :: acc) num_nodes [(mk_echo ("\"end_of_model\"") |> mk_command)] in *)
  let base = [(mk_echo ("\"end_of_model\"") |> mk_command)] in
  (* Compute eval statements for assertions *)
  let assertions =
    match eassert with
    | None -> base
    | Some _ ->
      AdjGraph.fold_vertices (fun u acc ->
          let assu = (assert_var u) ^ "-result" in
          let tm = mk_var (StringMap.find_default assu assu renaming) |> mk_term in
          let ev = mk_eval tm |> mk_command in
          let ec = mk_echo ("\"" ^ (var assu) ^ "\"")
                   |> mk_command in
          ec :: ev :: acc) num_nodes base
  in
  (* Compute eval statements for symbolic variables *)
  let symbols =
    VarMap.fold (fun sv _ acc ->
        let sv = symbolic_var sv in
        let tm = mk_var (StringMap.find_default sv sv renaming) |> mk_term in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ (var sv) ^ "\"") |> mk_command in
        ec :: ev :: acc) symbolics assertions in
  symbols

let parse_val (s : string) : Syntax.value =
  let lexbuf = Lexing.from_string s
  in
  try SMTParser.smtlib SMTLexer.token lexbuf
  with exn ->
    begin
      let tok = Lexing.lexeme lexbuf in
      failwith (Printf.sprintf "failed to parse string %s on %s" s tok)
    end

let translate_model (m : (string, string) BatMap.t) : Solution.t =
  BatMap.foldi (fun k v sol ->
      let nvval = parse_val v in
      match k with
      | k when BatString.starts_with k "label" ->
        {sol with labels= AdjGraph.VertexMap.add (node_of_label_var k) nvval sol.labels}
      | k when BatString.starts_with k "assert-" ->
        {sol with assertions=
                    match sol.assertions with
                    | None ->
                      Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                              (nvval |> Syntax.bool_of_val |> oget)
                              AdjGraph.VertexMap.empty)
                    | Some m ->
                      Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                              (nvval |> Syntax.bool_of_val |> oget) m)
        }
      | k ->
        let k_var = Var.of_var_string k in
        {sol with symbolics= VarMap.add k_var nvval sol.symbolics}) m
    {symbolics = VarMap.empty;
     labels = AdjGraph.VertexMap.empty;
     assertions= None}

let box_vals (xs : (int * Syntax.value) list) =
  match xs with
  | [(_,v)] -> v
  | _ ->
    vtuple (BatList.sort (fun (x1,x2) (y1,y2) -> compare x1 y1) xs
            |> BatList.map (fun (x,y) -> y))

let translate_model_unboxed (m : (string, string) BatMap.t) : Solution.t =
  let (symbolics, labels, assertions) =
    BatMap.foldi (fun k v (symbolics, labels, assertions) ->
        let nvval = parse_val v in
        match k with
        | k when BatString.starts_with k "label" ->
          (match proj_of_var k with
           | None ->
             ( symbolics,
               AdjGraph.VertexMap.add (node_of_label_var k) [(0,nvval)] labels,
               assertions )
           | Some i ->
             ( symbolics,
               AdjGraph.VertexMap.modify_def
                 [] (node_of_label_var k) (fun xs -> (i,nvval) :: xs) labels,
               assertions ))
        | k when BatString.starts_with k "assert-" ->
          ( symbolics,
            labels,
            match assertions with
            | None ->
              Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                      (nvval |> Syntax.bool_of_val |> oget)
                      AdjGraph.VertexMap.empty)
            | Some m ->
              Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                      (nvval |> Syntax.bool_of_val |> oget) m) )
        | k ->
          ( let new_symbolics = VarMap.add (Var.of_var_string k) nvval symbolics in
            new_symbolics, labels, assertions )
      ) m (VarMap.empty,AdjGraph.VertexMap.empty, None)
  in
  { symbolics = symbolics;
    labels = AdjGraph.VertexMap.map box_vals labels;
    assertions = assertions }


(* Model Refiners *)
let refineModelMinimizeFailures (model: Solution.t) info query chan
    solve renaming env net =
  match (get_requires_failures net.requires).e with
  | EOp(AtMost n, [e1;e2;e3]) ->
    (match e1.e with
     | ETuple es ->
       VarMap.iter (fun fvar fval ->
           match fval.v with
           | VBool b ->
             if b then
               Printf.printf "Initial model failed: %s\n" (Var.to_string fvar);
           | _ -> failwith "This should be a boolean variable") model.symbolics;
       let mult = smt_config.multiplicities in
       let arg2 =
         aexp(etuple (BatList.map (fun evar ->
             match evar.e with
             | EVar fvar ->
               let n = StringMap.find (Var.name fvar)
                   mult in
               (exp_of_value
                  (avalue (vint (Integer.of_int n),
                           Some (TInt 32),
                           Span.default)))
             | _ -> failwith "expected a variable") es),
              e2.ety,
              Span.default)
       in
       let new_req =
         aexp (eop (AtMost n) [e1; arg2;e3], Some TBool, Span.default) in
       let zes = Unboxed.encode_exp_z3 "" env new_req in
       let zes_smt =
         Unboxed.(to_list (lift1 (fun ze -> mk_assert ze |> mk_command) zes))
       in
       Some (commands_to_smt smt_config.verbose info zes_smt)
     | _ -> failwith "expected a tuple")
  | _ -> failwith "expected at most"

(** Refines the first model returned by the solver by asking if
    the counter example still holds when failing only the single
    links *)
(* TODO: Avoid using this until we have support for source nodes in min-cut *)
let refineModelWithSingles (model : Solution.t) info query chan solve renaming _ ds =
  (* Find and separate the single link failures from the rest *)
  let (failed, notFailed) =
    VarMap.fold (fun fvar fval (accFailed, accNotFailed) ->
        match fval.v with
        | VBool b ->
          if b then
            begin
              (* FIXME: I have no idea if Var.name is sufficient here.
                 A better option is probably to change smt_config.multiplicities
                 to be a VarMap. *)
              let fmult = StringMap.find (Var.name fvar) smt_config.multiplicities in
              if fmult > 1 then
                (accFailed, fvar :: accNotFailed)
              else
                (fvar :: accFailed, accNotFailed)
            end
          else (accFailed, fvar :: accNotFailed)
        | _ -> failwith "This should be a boolean variable") model.symbolics ([], [])
  in
  match failed with
  | [] -> None
  | _ ->
    let failed =
      BatList.map (fun fvar -> (mk_eq (mk_var (Var.to_string fvar)) (mk_bool true))
                               |> mk_term |> mk_assert |> mk_command) failed
      |> commands_to_smt smt_config.verbose info
    in
    let notFailed =
      BatList.map (fun fvar -> (mk_eq (mk_var (Var.to_string fvar)) (mk_bool false))
                               |> mk_term |> mk_assert |> mk_command) notFailed
      |> commands_to_smt smt_config.verbose info
    in
    Some (failed ^ notFailed)
