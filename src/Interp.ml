open Syntax
open Printing
open Printf

(* Interpreter Errors *)
(* Interpreter Environments *)

let empty_env = {ty= Env.empty; value= Env.empty}

let update_value env x v = {env with value= Env.update env.value x v}

let update_values env venv =
  {env with value= Env.updates env.value venv}

let update_ty env x t = {env with ty= Env.update env.ty x t}

let update_tys env tvs tys =
  let rec loop tenv tvs tys =
    match (tvs, tys) with
    | [], [] -> tenv
    | tv :: tvs, ty :: tys -> loop (Env.update tenv tv ty) tvs tys
    | _, _ -> failwith "wrong arity in type application"
  in
  {env with ty= loop env.ty tvs tys}

(* Equality of values *)
(* ignores type annotations when checking for equality *)
let rec equal_val v1 v2 =
  match (v1.v, v2.v) with
  | VBool b1, VBool b2 -> b1 = b2
  | VInt i1, VInt i2 -> Integer.equal i1 i2
  | VMap m1, VMap m2 -> BddMap.equal m1 m2
  | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
  | VOption None, VOption None -> true
  | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
  | VClosure _, _ -> failwith "internal error (equal_val)"
  | _, VClosure _ -> failwith "internal error (equal_val)"
  | _, _ -> false

and equal_vals vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | v1 :: rest1, v2 :: rest2 ->
      equal_val v1 v2 && equal_vals rest1 rest2
  | _, _ -> false

(* Expression and operator interpreters *)
(* matches p b is Some env if v matches p and None otherwise; assumes no repeated variables in pattern *)
let rec matches p (v: Syntax.value) : Syntax.value Env.t option =
  match (p, v.v) with
  | PWild, v -> Some Env.empty
  | PVar x, _ -> Some (Env.bind x v)
  | PBool true, VBool true -> Some Env.empty
  | PBool false, VBool false -> Some Env.empty
  | PInt i1, VInt i2 ->
      if Integer.equal i1 i2 then Some Env.empty else None
  | PTuple ps, VTuple vs -> matches_list ps vs
  | POption None, VOption None -> Some Env.empty
  | POption (Some p), VOption (Some v) -> matches p v
  | (PBool _ | PInt _ | PTuple _ | POption _), _ -> None

and matches_list ps vs =
  match (ps, vs) with
  | [], [] -> Some Env.empty
  | p :: ps, v :: vs -> (
    match matches p v with
    | None -> None
    | Some env1 ->
      match matches_list ps vs with
      | None -> None
      | Some env2 -> Some (Env.updates env2 env1) )
  | _, _ -> None

let rec match_branches branches v =
  match branches with
  | [] -> None
  | (p, e) :: branches ->
    match matches p v with
    | Some env -> Some (env, e)
    | None -> match_branches branches v

module ExpMap = Map.Make (struct
  type t = exp

  let compare = Pervasives.compare
end)

let build_env (env: env) (free_vars: Var.t BatSet.PSet.t) :
    value BatSet.PSet.t =
  let base = BatSet.PSet.create compare_values in
  BatSet.PSet.fold
    (fun v acc ->
      match Env.lookup_opt env.value v with
      | Some value -> BatSet.PSet.add value acc
      | None -> acc )
    free_vars base

let bddfunc_cache = ref ExpMap.empty

let rec interp_exp env e =
  match e.e with
  | ETy (e, _) -> interp_exp env e
  | EVar x -> (
    match Env.lookup_opt env.value x with
    | None ->
        failwith
          (Printf.sprintf "runtime exception - unbound variable: %s"
             (Var.to_string x))
    | Some v -> v )
  | EVal v -> v
  | EOp (op, es) -> interp_op env (oget e.ety) op es
  | EFun f -> vclosure (env, f)
  | EApp (e1, e2) -> (
      let v1 = interp_exp env e1 in
      let v2 = interp_exp env e2 in
      match v1.v with
      | VClosure (c_env, f) ->
          interp_exp (update_value c_env f.arg v2) f.body
      | _ -> failwith "bad functional application" )
  | EIf (e1, e2, e3) -> (
    match (interp_exp env e1).v with
    | VBool true -> interp_exp env e2
    | VBool false -> interp_exp env e3
    | _ -> failwith "bad if condition" )
  | ELet (x, e1, e2) ->
      let v1 = interp_exp env e1 in
      interp_exp (update_value env x v1) e2
  | ETuple es -> vtuple (List.map (interp_exp env) es)
  | ESome e -> voption (Some (interp_exp env e))
  | EMatch (e1, branches) ->
      let v = interp_exp env e1 in
      match match_branches branches v with
      | Some (env2, e) -> interp_exp (update_values env env2) e
      | None ->
          failwith
            ( "value " ^ value_to_string v
            ^ " did not match any pattern in match statement" )

and interp_op env ty op es =
  (* if arity op != List.length es then
    failwith
      (sprintf "operation %s has arity %d not arity %d"
         (op_to_string op) (arity op) (List.length es)) ; *)
  let vs = List.map (interp_exp env) es in
  match (op, vs) with
  | And, [{v= VBool b1}; {v= VBool b2}] -> vbool (b1 && b2)
  | Or, [{v= VBool b1}; {v= VBool b2}] -> vbool (b1 || b2)
  | Not, [{v= VBool b1}] -> vbool (not b1)
  | UAdd _, [{v= VInt i1}; {v= VInt i2}] ->
      vint (Integer.add i1 i2)
  | UEq, [v1; v2] ->
      if equal_values ~cmp_meta:false v1 v2 then vbool true
      else vbool false
  | ULess _, [{v= VInt i1}; {v= VInt i2}] ->
      if Integer.lt i1 i2 then vbool true else vbool false
  | ULeq _, [{v= VInt i1}; {v= VInt i2}] ->
      if Integer.leq i1 i2 then vbool true else vbool false
  | MCreate, [v] -> (
    match get_inner_type ty with
    | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
    | _ -> failwith "runtime error: missing map key type" )
  | MGet, [{v= VMap m}; v] -> BddMap.find m v
  | MSet, [{v= VMap m}; vkey; vval] ->
      vmap (BddMap.update m vkey vval)
  | MMap, [{v= VClosure (c_env, f)}; {v= VMap m}] ->
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
      let free = Syntax.free seen f.body in
      let env = build_env c_env free in
      vmap
        (BddMap.map ~op_key:(f.body, env)
           (fun v -> apply c_env f v)
           m)
  | ( MMerge
    , {v= VClosure (c_env, f)}
      :: {v= VMap m1} :: {v= VMap m2} :: rest )
    -> (
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
      let env = build_env c_env (Syntax.free seen f.body) in
      (* TO DO:  Need to preserve types in VOptions here ? *)
      let f_lifted v1 v2 =
        match apply c_env f v1 with
        | {v= VClosure (c_env, f)} -> apply c_env f v2
        | _ -> failwith "internal error (interp_op)"
      in
      match rest with
      | [el0; el1; er0; er1] ->
          let opt = (el0, el1, er0, er1) in
          vmap
            (BddMap.merge ~opt ~op_key:(f.body, env) f_lifted m1 m2)
      | _ -> vmap (BddMap.merge ~op_key:(f.body, env) f_lifted m1 m2)
      )
  | ( MMapFilter
    , [ {v= VClosure (c_env1, f1)}
      ; {v= VClosure (c_env2, f2)}
      ; {v= VMap m} ] ) ->
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
      let env = build_env c_env2 (Syntax.free seen f2.body) in
      let mtbdd =
        match ExpMap.find_opt f1.body !bddfunc_cache with
        | None -> (
            let bddf = BddFunc.create_value (oget f1.argty) in
            let env = Env.update Env.empty f1.arg bddf in
            let bddf = BddFunc.eval env f1.body in
            match bddf with
            | BBool bdd ->
                let mtbdd = BddFunc.wrap_mtbdd bdd in
                bddfunc_cache :=
                  ExpMap.add f1.body mtbdd !bddfunc_cache ;
                mtbdd
            | _ -> failwith "impossible" )
        | Some bddf -> bddf
      in
      let f v = apply c_env2 f2 v in
      vmap (BddMap.map_when ~op_key:(f2.body, env) mtbdd f m)
  | _, _ ->
      failwith
        (Printf.sprintf "bad operator application: %s"
           (Printing.op_to_string op))

and apply env f v = interp_exp (update_value env f.arg v) f.body

let interp e = interp_exp empty_env e

let interp = MemoizeExp.memoize ~size:1000 interp

let interp_closure cl (args: value list) =
  interp (Syntax.apply_closure cl args)

  
(** * Partial Interpreter *)

let rec interp_exp_partial env e =
  match e.e with
  | ETy (e, _) -> interp_exp_partial env e
  | EVar x -> (
    match Env.lookup_opt env.value x with
    | None -> e
    | Some v ->
       e_val v)
  | EVal v -> e
  | EOp (op, es) ->
     interp_op_partial env (oget e.ety) op es
  | EFun f ->
     (* This is kind of a hack: I think it only works if you inline
        functions, because it only applies to top-level definitions -
        otherwise the closure (env) is wrong *)
     (* exp_of_value (vclosure (env, {f with body = interp_exp_partial env f.body})) *)
     e
  | EApp (e1, e2) ->
    let pe1 = interp_exp_partial env e1 in
    let pe2 = interp_exp_partial env e2 in
    (match pe1.e with
     | EFun f ->
        if is_value pe2 then
          (*   interp_exp_partial (update_value c_env f.arg (to_value pe2)) f.body *)
          interp_exp_partial (update_value env f.arg (to_value pe2)) f.body
        else
          eapp pe1 pe2
     | _ -> failwith ("bad functional application: " ^ (show_exp ~show_meta:false e1)) )
  | EIf (e1, e2, e3) -> (
    let pe1 = interp_exp_partial env e1 in
    if is_value pe1 then
      (match (to_value pe1).v with
       | VBool true  -> interp_exp_partial env e2
       | VBool false -> interp_exp_partial env e3
       | _ -> failwith "bad if condition")
    else
      eif pe1 (interp_exp_partial env e2) (interp_exp_partial env e3))
  | ELet (x, e1, e2) ->
     let pe1 = interp_exp_partial env e1 in
     if is_value pe1 then
       interp_exp_partial (update_value env x (to_value pe1)) e2
     else
       elet x pe1 (interp_exp_partial env e2)
  | ETuple es ->
     etuple (List.map (interp_exp_partial env) es)
  | ESome e -> esome (interp_exp_partial env e)
  | EMatch (e1, branches) ->
     let pe1 = interp_exp_partial env e1 in
     if is_value pe1 then
       (match match_branches branches (to_value pe1) with
        | Some (env2, e) -> interp_exp_partial (update_values env env2) e
        | None ->
           failwith
             ( "value " ^ value_to_string (to_value pe1)
               ^ " did not match any pattern in match statement"))
     else
       ematch pe1 (List.map (fun (p,eb) -> (p, interp_exp_partial env eb)) branches)
and interp_op_partial env ty op es =
  (* if arity op != List.length es then
    failwith
      (sprintf "operation %s has arity %d not arity %d"
         (op_to_string op) (arity op) (List.length es)) ; *)
  let pes = List.map (interp_exp_partial env) es in
  if List.exists (fun pe -> not (is_value pe)) pes then
    eop op pes
  else
    begin
      exp_of_value @@ 
      match (op, List.map to_value pes) with
      | And, [{v= VBool b1}; {v= VBool b2}] -> vbool (b1 && b2)
      | Or, [{v= VBool b1}; {v= VBool b2}] -> vbool (b1 || b2)
      | Not, [{v= VBool b1}] -> vbool (not b1)
      | UAdd _, [{v= VInt i1}; {v= VInt i2}] ->
         vint (Integer.add i1 i2)
      | UEq, [v1; v2] ->
         if equal_values ~cmp_meta:false v1 v2 then vbool true
         else vbool false
      | ULess _, [{v= VInt i1}; {v= VInt i2}] ->
         if Integer.lt i1 i2 then vbool true else vbool false
      | ULeq _, [{v= VInt i1}; {v= VInt i2}] ->
         if Integer.leq i1 i2 then vbool true else vbool false
      | MCreate, [v] -> (
        match get_inner_type ty with
        | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
        | _ -> failwith "runtime error: missing map key type" )
      | MGet, [{v= VMap m}; v] -> BddMap.find m v
      | MSet, [{v= VMap m}; vkey; vval] ->
         vmap (BddMap.update m vkey vval)
      | MMap, [{v= VClosure (c_env, f)}; {v= VMap m}] ->
         let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
         let free = Syntax.free seen f.body in
         let env = build_env c_env free in
         vmap
           (BddMap.map ~op_key:(f.body, env)
                       (fun v -> apply c_env f v)
                       m)
      | ( MMerge
        , {v= VClosure (c_env, f)}
          :: {v= VMap m1} :: {v= VMap m2} :: rest )
        -> (
        let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
        let env = build_env c_env (Syntax.free seen f.body) in
        (* TO DO:  Need to preserve types in VOptions here ? *)
        let f_lifted v1 v2 =
          match apply c_env f v1 with
          | {v= VClosure (c_env, f)} -> apply c_env f v2
          | _ -> failwith "internal error (interp_op)"
        in
        match rest with
        | [el0; el1; er0; er1] ->
           let opt = (el0, el1, er0, er1) in
           vmap
             (BddMap.merge ~opt ~op_key:(f.body, env) f_lifted m1 m2)
        | _ -> vmap (BddMap.merge ~op_key:(f.body, env) f_lifted m1 m2)
      )
      | ( MMapFilter
        , [ {v= VClosure (c_env1, f1)}
          ; {v= VClosure (c_env2, f2)}
          ; {v= VMap m} ] ) ->
         let seen = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
         let env = build_env c_env2 (Syntax.free seen f2.body) in
         let mtbdd =
           match ExpMap.find_opt f1.body !bddfunc_cache with
           | None -> (
             let bddf = BddFunc.create_value (oget f1.argty) in
             let env = Env.update Env.empty f1.arg bddf in
             let bddf = BddFunc.eval env f1.body in
             match bddf with
             | BBool bdd ->
                let mtbdd = BddFunc.wrap_mtbdd bdd in
                bddfunc_cache :=
                  ExpMap.add f1.body mtbdd !bddfunc_cache ;
                mtbdd
             | _ -> failwith "impossible" )
           | Some bddf -> bddf
         in
         let f v = apply c_env2 f2 v in
         vmap (BddMap.map_when ~op_key:(f2.body, env) mtbdd f m)
      | _, _ ->
         failwith
           (Printf.sprintf "bad operator application: %s"
                           (Printing.op_to_string op))
    end
    
let interp_partial = fun e -> interp_exp_partial empty_env e

(* let interp_partial_closure cl (args: value list) = *)
(*   interp_partial (Syntax.apply_closure cl args) *)

let interp_partial = MemoizeExp.memoize ~size:1000 interp_partial

let interp_partial_fun (fn : Syntax.exp) (args: value list) =
  Syntax.apps fn (List.map (fun a -> e_val a) args) |>
    interp_partial
  
