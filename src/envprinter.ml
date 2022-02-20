open Ast
open Environment

let pp_env fmt (e : env) =
  Format.fprintf fmt "Context:\n";
  List.iter
    (fun (name, s) -> 
      Format.fprintf fmt "\t%s:%a\n" 
        name
        pp_sort s
    ) e.context;
  Format.fprintf fmt "\n\n";
  Format.fprintf fmt "Goal:\n";
  Format.fprintf fmt "\t%a\n\n"
    pp_sort e.target
