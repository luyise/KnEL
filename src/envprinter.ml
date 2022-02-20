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
  Format.fprintf fmt "\x1B[36mContext:\x1B[39m\n%a"
    pp_context e.context;
  Format.fprintf fmt "\n";
  Format.fprintf fmt "\x1B[36mGoal:\x1B[39m\n";
  Format.fprintf fmt "\t%a\n\n"
    pp_sort e.target
