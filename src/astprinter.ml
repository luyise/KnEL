open Ast

let rec pp_sort fmt (s : sort) =
  match s with
    | SVar id -> Format.fprintf fmt "%a" 
        pp_ident id
    | SFun (a , b) -> Format.fprintf fmt "(%a → %a)"
        pp_sort a
        pp_sort b
    | SProd a_list -> 
        begin match a_list with
          | [] -> Format.fprintf fmt "⊤"
          | [ a ] -> Format.fprintf fmt "×[ %a ]"
              pp_sort a
          | _ -> 
              begin
              Format.fprintf fmt "×[ ";
              let rec print_sort_list s_list =
                match s_list with
                  | [] -> failwith "unexpected"
                  | [ a ] -> Format.fprintf fmt "%a ]"
                      pp_sort a
                  | a :: s_tail -> 
                      Format.fprintf fmt "%a , "
                        pp_sort a;
                      print_sort_list s_tail
              in print_sort_list a_list
              end
        end
    | SSum a_list -> 
        begin match a_list with
          | [] -> Format.fprintf fmt "⊥"
          | [ a ] -> Format.fprintf fmt "+[ %a ]"
              pp_sort a
          | _ ->
              Format.fprintf fmt "+[ ";
              let rec print_sort_list s_list =
                match s_list with
                  | [] -> failwith "unexpected"
                  | [ a ] -> Format.fprintf fmt "%a ]"
                      pp_sort a
                  | a :: s_tail -> 
                      Format.fprintf fmt "%a , "
                        pp_sort a;
                      print_sort_list s_tail
              in print_sort_list a_list
        end

let rec pp_term fmt (t : term) =
  match t with
    | TVar id -> Format.fprintf fmt "%a" 
        pp_ident id
    | TLam ((id , s) , y) -> Format.fprintf fmt "(λ (%a : %a) → %a)"
        pp_ident id
        pp_sort s
        pp_term y
    | TApp (x , y) -> Format.fprintf fmt "%a %a"
        pp_term x
        pp_term y
    | TProdConstr x_list ->
        begin match x_list with
          | [] -> Format.fprintf fmt "*"
          | [ x ] -> Format.fprintf fmt "( %a )"
              pp_term x
          | _ ->
              Format.fprintf fmt "( ";
              let rec print_term_list s_list =
                match x_list with
                  | [] -> failwith "unexpected"
                  | [ x ] -> Format.fprintf fmt "%a )"
                      pp_term x
                  | x :: x_tail -> 
                      Format.fprintf fmt "%a , "
                        pp_term x;
                      print_term_list x_tail
              in print_term_list x_list
        end
    | TSumConstr (n , x , _) ->
        Format.fprintf fmt "(in %d %a)"
          n
          pp_term x

let pp_var fmt varl =
  Format.fprintf fmt "Variables = {\n";
  List.iter
    (fun (name, top) -> match top with 
      | None -> Format.fprintf fmt "\t%s\n" name
      | Some t -> Format.fprintf fmt "\t%s : ()\n" name)
    varl;
  Format.fprintf fmt "}\n\n"

let pp_thm fmt (name, stmt, proof) =
  Format.fprintf fmt
  "Theorem %s:\n%a\n%s\n\n"
    name
    pp_sort stmt
    proof

let pp_file fmt (var, thm_list) =
  pp_var fmt var;
  List.iter (pp_thm fmt) thm_list
