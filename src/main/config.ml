
let html_view = ref false
let shutdown = ref false
let verbose = ref false
let set_debug_mode = fun () -> verbose := true; Printexc.record_backtrace true

let options = [
  "--stop",       Arg.Set shutdown,     "stop the program";
  "--html-view",  Arg.Set html_view,  "display html as output";
  "-v",           Arg.Set verbose,    "enable verbose mode";
  "-d",           Arg.Unit set_debug_mode, "enable debug the compiler mode";
]

let usage = "usage : main.exe file.knl"

let parse_arguments f = Arg.parse options f usage