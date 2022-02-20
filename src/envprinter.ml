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
  Format.fprintf fmt "Context:\n%a"
    pp_context e.context;
  Format.fprintf fmt "\n";
  Format.fprintf fmt "Goal:\n";
  Format.fprintf fmt "\t%a\n\n"
    pp_sort e.target
