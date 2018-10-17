open Syntax
open Unsigned

type network =
  { attr_type : Syntax.ty;
    init      : Syntax.exp;
    trans     : Syntax.exp;
    merge     : Syntax.exp;
    assertion : Syntax.exp;
    graph     : Graph.t;
  }
   
type prefix = Unsigned.UInt32.t * Unsigned.UInt32.t

let printPrefix ((ip, pre) : prefix) =
  Printf.sprintf "(%d, %d)" (UInt32.to_int ip) (UInt32.to_int pre)

let printPrefixes (prefixes : prefix BatSet.t) =
  "{" ^ BatSet.fold (fun pre acc -> (printPrefix pre) ^ "," ^ acc) prefixes "}"
            
let partialEvalOverNodes (g : Graph.t) (e: Syntax.exp) =
  let tbl = Hashtbl.create (Unsigned.UInt32.to_int (Graph.num_vertices g)) in
  Graph.fold_vertices
    (fun u _ ->
      let initu = Interp.interp_partial (Syntax.apps e [e_val (vint u)]) in
      Hashtbl.add tbl u initu) g ();
  tbl

(* deprecated *)
let get_prefixes_from_val (dictv : Syntax.value) : prefix list =
  match dictv.v with
  | VMap dict ->
     List.map (fun (prefixv, _) ->
         match prefixv.v with
         | VTuple [ipv; prev] ->
            (match ipv.v, prev.v with
             | VUInt32 ip, VUInt32 pre -> (ip, pre)
             | _, _ -> failwith "not a concrete prefix")
         | _ -> failwith "expected a tuple") (fst (BddMap.bindings dict))
  | _ -> failwith "value is not a dict"

let build_prefix_map (u : Unsigned.UInt32.t)
                     (prefixes: prefix BatSet.t)
                     (acc : (prefix, Graph.Vertex.t BatSet.t) BatMap.t):
      (prefix, Graph.Vertex.t BatSet.t) BatMap.t =
  BatSet.fold (fun pre acc ->
      BatMap.modify_def BatSet.empty pre (fun us -> BatSet.add u us) acc)
              prefixes acc

(* Finds the prefixes used by an expression *)
let get_prefixes_from_expr (expr: Syntax.exp) : prefix BatSet.t =
  let prefixes = ref BatSet.empty in
  Visitors.iter_exp (fun e ->
      match e.e with
      | EOp (UEq, [var; pre]) when is_value pre ->
         (match var.e with
          | EVar x ->
             if (Var.name x) = "d" then
               begin
                 match (Syntax.to_value pre).v with
                 | VTuple [v1;v2] ->
                    (match v1.v, v2.v with
                     | VUInt32 ip, VUInt32 p ->
                        prefixes := BatSet.add (ip, p) !prefixes
                     | _ -> ())
                 | _ -> ()
               end
             else ()
          | _ -> ())
      | _ -> ()) expr;
  !prefixes
  
let relevantPrefixes (assertionTable : (Unsigned.UInt32.t, Syntax.exp) Hashtbl.t) =
  Hashtbl.fold (fun _ eu acc ->
      let prefixes = get_prefixes_from_expr eu in
      BatSet.union prefixes acc) assertionTable BatSet.empty

let partialEvalInit (n : network) =
  partialEvalOverNodes n.graph n.init

let partialEvalAssert (n : network) =
  partialEvalOverNodes n.graph n.assertion

let get_prefixes_from_expr (expr: Syntax.exp) : prefix BatSet.t =
  let prefixes = ref BatSet.empty in
  Visitors.iter_exp (fun e ->
      match e.e with
      | EOp (UEq, [var; pre]) when is_value pre ->
         (match var.e with
          | EVar x ->
             if (Var.name x) = "d" then
               begin
                 match (Syntax.to_value pre).v with
                 | VTuple [v1;v2] ->
                    (match v1.v, v2.v with
                     | VUInt32 ip, VUInt32 p ->
                        prefixes := BatSet.add (ip, p) !prefixes
                     | _ -> ())
                 | _ -> ()
               end
             else ()
          | _ -> ())
      | _ -> ()) expr;
  !prefixes
  
(* Currently this will only work with networks generated by batfish. *)
let findInitialSlices initTbl =
  Hashtbl.fold
    (fun u initu acc ->
      let prefixes = get_prefixes_from_expr initu in
      build_prefix_map u prefixes acc) initTbl BatMap.empty

(* let sliceAssertion (prefixes : prefix BatSet.t) *)
(*                    (assertionTable : (Unsigned.UInt32.t, Syntax.exp) Hashtbl.t) = *)
  
