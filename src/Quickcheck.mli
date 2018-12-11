open Collections
open Generators
open Syntax

type check_stats = {iterations: int; num_rejected: int}

val check_random :
  declarations -> iterations:int -> Solution.t option * check_stats

(* val check_smart : *)
(*      Console.info *)
(*   -> declarations *)
(*   -> iterations:int *)
(*   -> Solution.t option * check_stats *)
