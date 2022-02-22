open Ast
open Astprinter
open Environment

let pp_env fmt (e : env) =
  Format.fprintf fmt "\x1B[38;5;130mContext:\x1B[39m\n%a"
    pp_context e.context;
  Format.fprintf fmt "\n";
  Format.fprintf fmt "\x1B[38;5;130mGoal:\x1B[39m\n";
  Format.fprintf fmt "\t%a\n\n"
    pp_sort e.target
