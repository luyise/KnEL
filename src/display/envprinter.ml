open Parse
open Ast
open Astprinter
open Environment

let pp_def fmt (defs : (ident * expr) list) =
  if !Config.html_view then begin
    Format.fprintf fmt "<br><br>";
    let f =
      (fun (name, term) ->
        Format.fprintf fmt "<p style = \"margin-top: -12px; margin-left: 30px; text-indent: -15px\" >";
        Format.fprintf fmt "%a %a %a"
          (pp_ident CLR_nam) name
          (pp_ident CLR_def) "="
          pp_expr term;
        Format.fprintf fmt "</p>"
      )
    in
    List.iter f (List.rev defs)
  end else begin
    let f =
      (fun (name, term) ->
        Format.fprintf fmt "\t%a %a %a\n" 
          (pp_ident CLR_nam) name
          (pp_ident CLR_def) "="
          pp_expr term)
    in
    List.iter f (List.rev defs)
  end

let pp_env fmt (e : env) =
  if !Config.html_view
  then begin
    Format.fprintf fmt "<br><br><b style=\"color:#af601a\">Context:</b> %a"
      pp_context e.context;
    Format.fprintf fmt "<b style=\"color:#af601a\">Definitions:</b> %a"
      pp_def e.definitions;
    Format.fprintf fmt "<b style=\"color:#af601a\">Goal: </b>";
    Format.fprintf fmt "<br><br><p style = \"margin-top: -12px; margin-left: 30px; text-indent: -15px\" >%a</p>"
      pp_expr e.target;
  end else begin
    Format.fprintf fmt "\x1B[1m\x1B[38;5;130mContext:\x1B[39m\x1B[22m\n%a"
      pp_context e.context;
    Format.fprintf fmt "\n";
    Format.fprintf fmt "\x1B[1m\x1B[38;5;130mDefinitions:\x1B[39m\x1B[22m\n%a"
      pp_def e.definitions;
    Format.fprintf fmt "\n";
    Format.fprintf fmt "\x1B[1m\x1B[38;5;130mGoal:\x1B[39m\x1B[22m\n";
    Format.fprintf fmt "\t%a\n\n"
      pp_expr e.target
  end
