open Ast

let pp_var fmt varl =
  Format.fprintf fmt "Variables = {\n";
  List.iter
    (fun (name, top) -> match top with 
      | None -> Format.fprintf fmt "\t%s\n" name
      | Some t -> Format.fprintf fmt "\t%s:()\n" name)
    varl;
  Format.fprintf fmt "}\n\n"

let pp_thm fmt (name, stmt, proof) =
  Format.fprintf fmt
  "Theorem %s:\n%a\n%s\n\n"
    name
    pp_place stmt
    proof

let pp_file fmt (var, thm_list) =
  pp_var fmt var;
  List.iter (pp_thm fmt) thm_list
