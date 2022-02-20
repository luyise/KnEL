open Ast
open Astprinter
open Environment

let pp_context fmt (ctx : context) =
  List.iter
    (fun (name, s) -> 
      Format.fprintf fmt "\t%s : %a\n" 
        name
        pp_sort s
    ) ctx

let pp_env fmt (e : env) =
  Format.fprintf fmt "\x1B[36mContext:\n%a\x1B[39m"
    pp_context e.context;
  Format.fprintf fmt "\n";
  Format.fprintf fmt "\x1B[36mGoal:\n\x1B[39m";
  Format.fprintf fmt "\t%a\n\n"
    pp_sort e.target
