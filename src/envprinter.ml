open Ast
open Astprinter
open Environment

let pp_context fmt (ctx : context) =
  let f =
    if !Config.html_view
    then
      (fun (name, s) -> 
        Format.fprintf fmt "<p style=\"text-indent:20px;\">%s : %a</p>"
          name
          pp_sort s)
    else
      (fun (name, s) ->
        Format.fprintf fmt "\t%s : %a\n" 
          name
          pp_sort s)
  in
  List.iter f ctx

let pp_env fmt (e : env) =
  if !Config.html_view
  then begin
    Format.fprintf fmt "<h3 style=\"color:#FF0000\";>Context:</h3>%a"
      pp_context e.context;
    Format.fprintf fmt "<h3 style=\"color:#FF0000\";>Goal:</h3>";
    Format.fprintf fmt "<p>%a</p>"
      pp_sort e.target
  end else begin
    Format.fprintf fmt "\x1B[36mContext:\x1B[39m\n%a"
      pp_context e.context;
    Format.fprintf fmt "\n";
    Format.fprintf fmt "\x1B[36mGoal:\x1B[39m\n";
    Format.fprintf fmt "\t<p style=\"text-indent:20px;\">%a</p>\n\n"
      pp_sort e.target
  end
