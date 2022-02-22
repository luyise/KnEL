
let html_view = ref false
let shutdown = ref false

let options = [
  "--stop",       Arg.Set shutdown,     "stop the program";
  "--html-view",  Arg.Set html_view,  "display html as output";
]

let usage = "usage : main.exe file.knl"

let parse_arguments f = Arg.parse options f usage