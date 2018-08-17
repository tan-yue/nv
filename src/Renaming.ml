open Collections
open Syntax

let map_back bmap x y =
  bmap := StringMap.add (Var.to_string y) (Var.to_string x) !bmap

let fresh x = Var.fresh (Var.to_string x)

let rec update_pattern (env: Var.t Env.t) (p: pattern) :
    pattern * Var.t Env.t =
  match p with
  | PWild | PBool _ | PUInt32 _ -> (p, env)
  | PVar x ->
      let y = fresh x in
      (PVar y, Env.update env x y)
  | PTuple ps ->
      let env, ps = List.fold_left add_pattern (env, []) ps in
      (PTuple (List.rev ps), env)
  | POption None -> (p, env)
  | POption (Some p) ->
      let p', env = update_pattern env p in
      (POption (Some p'), env)

and add_pattern (env, ps) p =
  let p', env' = update_pattern env p in
  (env', p' :: ps)

let rec alpha_convert_exp (env: Var.t Env.t) (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e);
  Printf.printf "type: %s\n" (Printing.ty_to_string (oget e.ety)); *)
  match e.e with
  | EVar x -> EVar (Env.lookup env x) |> wrap e
  | EVal v -> e
  | EOp (op, es) ->
      EOp (op, List.map (fun e -> alpha_convert_exp env e) es)
      |> wrap e
  | EFun f ->
      let x = fresh f.arg in
      let e' = alpha_convert_exp (Env.update env f.arg x) f.body in
      EFun {f with arg= x; body= e'} |> wrap e
  | EApp (e1, e2) ->
      EApp (alpha_convert_exp env e1, alpha_convert_exp env e2)
      |> wrap e
  | EIf (e1, e2, e3) ->
      EIf
        ( alpha_convert_exp env e1
        , alpha_convert_exp env e2
        , alpha_convert_exp env e3 )
      |> wrap e
  | ELet (x, e1, e2) ->
      let e1' = alpha_convert_exp env e1 in
      let y = fresh x in
      let e2' = alpha_convert_exp (Env.update env x y) e2 in
      ELet (y, e1', e2') |> wrap e
  | ETuple es ->
      ETuple (List.map (fun e -> alpha_convert_exp env e) es)
      |> wrap e
  | ESome e1 -> ESome (alpha_convert_exp env e1) |> wrap e
  | EMatch (e, bs) ->
      let bs' =
        List.map
          (fun (p, e) ->
            let p, env = update_pattern env p in
            (p, alpha_convert_exp env e) )
          bs
      in
      EMatch (alpha_convert_exp env e, bs') |> wrap e
  | ETy (e1, ty) -> ETy (alpha_convert_exp env e1, ty) |> wrap e

let alpha_convert_declaration bmap (env: Var.t Env.t)
    (d: declaration) =
  match d with
  | DLet (x, tyo, e) ->
      let y = fresh x in
      let env = Env.update env x y in
      let e = alpha_convert_exp env e in
      (env, DLet (y, tyo, e))
  | DSymbolic (x, Exp e) ->
      let y = fresh x in
      map_back bmap x y ;
      let env = Env.update env x y in
      let e = alpha_convert_exp env e in
      (env, DSymbolic (y, Exp e))
  | DSymbolic (x, Ty ty) ->
      let y = fresh x in
      map_back bmap x y ;
      let env = Env.update env x y in
      (env, DSymbolic (y, Ty ty))
  | DMerge e -> (env, DMerge (alpha_convert_exp env e))
  | DTrans e -> (env, DTrans (alpha_convert_exp env e))
  | DInit e -> (env, DInit (alpha_convert_exp env e))
  | DAssert e -> (env, DAssert (alpha_convert_exp env e))
  | DRequire e -> (env, DRequire (alpha_convert_exp env e))
  | DATy _ | DNodes _ | DEdges _ -> (env, d)

let rec alpha_convert_aux bmap env (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = alpha_convert_declaration bmap env d in
      d' :: alpha_convert_aux bmap env' ds'

let update_symbolics bmap smap =
  StringMap.fold
    (fun s v acc ->
      match StringMap.find_opt s bmap with
      | None -> StringMap.add s v acc
      | Some k -> StringMap.add k v acc )
    smap StringMap.empty

let adjust_solution bmap (s: Solution.t) =
  {s with symbolics= update_symbolics bmap s.symbolics}

let rec alpha_convert_declarations (ds: declarations) =
  Var.reset () ;
  let bmap = ref StringMap.empty in
  let prog = alpha_convert_aux bmap Env.empty ds in
  (prog, adjust_solution !bmap)
