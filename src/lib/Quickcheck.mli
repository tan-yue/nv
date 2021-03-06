type check_stats = {iterations: int; num_rejected: int}

val check_random :
  Nv_lang.Syntax.network -> iterations:int -> Nv_solution.Solution.t option * check_stats

val check_smart :
     Nv_lang.Console.info -> Nv_lang.Syntax.network -> iterations:int -> Nv_solution.Solution.t option * check_stats
