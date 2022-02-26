open Astprinter
open Environment


let pp_env fmt (e : env) =
  if !Config.html_view
  then begin
    Format.fprintf fmt "<h3 style=\"color:#FF0000\";>Context:</h3>%a"
      pp_context e.context;
    Format.fprintf fmt "<h3 style=\"color:#FF0000\";>Goal:</h3>";
    Format.fprintf fmt "<p style=\"text-indent:20px;\">%a</p>"
      pp_expr e.target
  end else begin
    Format.fprintf fmt "\x1B[1m\x1B[38;5;130mContext:\x1B[39m\x1B[22m\n%a"
      pp_context e.context;
    Format.fprintf fmt "\n";
    Format.fprintf fmt "\x1B[1m\x1B[38;5;130mGoal:\x1B[39m\x1B[22m\n";
    Format.fprintf fmt "\t%a\n\n"
      pp_expr e.target
  end
