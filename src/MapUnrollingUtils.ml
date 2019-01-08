open Syntax
open Collections

type maplist = (Syntax.ty * ExpSet.t) list;;

let maplist_to_string (lst : maplist) =
  let entry_to_string (ty, keys) =
    "( " ^ Printing.ty_to_string ty ^ ", [ " ^
    (ExpSet.fold
       (fun e s -> s ^ Printing.exp_to_string e ^ "; ")
       keys "")
    ^ "] )"
  in
  "[ " ^
  (List.fold_left (fun s1 s2 -> s1 ^ s2 ^ "; ") "" @@
   List.map entry_to_string lst)
  ^ " ]"
;;

let rec add_to_maplist (ty, keys) lst : maplist =
  match lst with
  | [] -> [(ty, keys)]
  | (ty2, keys2) :: tl ->
    if Typing.equiv_tys ty ty2 then
      (ty, ExpSet.union keys keys2) :: tl
    else
      (ty2, keys2) :: add_to_maplist (ty, keys) tl
;;

let add_if_map_type (ty, keys) lst : maplist =
  match Typing.canonicalize_type ty with
  | TMap (ty1, ty2) ->
    add_to_maplist (TMap (ty1, ty2), keys) lst
  | _ -> lst
;;

let rec collect_in_exp (exp : Syntax.exp) (acc : maplist) : maplist =
  (* print_endline @@ "Collecting in expr " ^ Printing.exp_to_string exp; *)
  let curr_ty = oget exp.ety in
  (* If our current expression has map type, add that to our list *)
  let acc = add_if_map_type (curr_ty, ExpSet.empty) acc in
  match exp.e with
  | EVar _
  | EVal _ -> acc
  | EOp (op, es) ->
    begin
      (* Collect key if necessary *)
      let acc =
        match op, es with
        | MGet, [m; key]
        | MSet, [m; key; _] ->
          add_if_map_type ((oget m.ety), ExpSet.singleton key) acc
        | _ -> acc
      in
      List.fold_left (BatPervasives.flip collect_in_exp) acc es
    end
  | EFun f ->
    collect_in_exp f.body acc
  | ELet (_, e1, e2)
  | EApp (e1, e2) ->
    acc
    |> collect_in_exp e1
    |> collect_in_exp e2
  | EIf (e1, e2, e3) ->
    acc
    |> collect_in_exp e1
    |> collect_in_exp e2
    |> collect_in_exp e3
  | ETuple es ->
    List.fold_left (BatPervasives.flip collect_in_exp) acc es
  | ERecord map ->
    StringMap.fold (fun _ -> collect_in_exp) map acc
  | EProject _ -> failwith ""
  | ESome e ->
    collect_in_exp e acc
  | EMatch (e, branches) ->
    let acc = collect_in_exp e acc in
    List.fold_left
      (fun acc (_, exp) ->
         collect_in_exp exp acc)
      acc branches
  | ETy (e, _) ->
    collect_in_exp e acc
;;

let collect_in_decl (d : declaration) (acc : maplist): maplist =
  (* print_endline @@ "Collecting in decl " ^ Printing.declaration_to_string d; *)
  match d with
  | DLet (_, tyo, exp) ->
    add_if_map_type (oget tyo, ExpSet.empty) acc
    |> collect_in_exp exp
  | DSymbolic (_, toe) ->
    begin
      match toe with
      | Ty ty ->
        add_if_map_type (ty, ExpSet.empty) acc
      | Exp exp -> collect_in_exp exp acc
    end
  | DATy ty ->
    add_if_map_type (ty, ExpSet.empty) acc
  | DUserTy (_, ty) ->
    add_if_map_type (ty, ExpSet.empty) acc
  | DMerge exp
  | DTrans exp
  | DInit exp
  | DAssert exp
  | DRequire exp ->
    collect_in_exp exp acc
  | DNodes _
  | DEdges _ ->
    acc
;;

(* Given a program on which type inference has been run, goes through
   it and returns a list of each map type which appears in that program,
   combined with the set of keys used for that map type. *)
let collect_map_types_and_keys (decls : declarations) : maplist =
  List.fold_left (BatPervasives.flip collect_in_decl) [] decls