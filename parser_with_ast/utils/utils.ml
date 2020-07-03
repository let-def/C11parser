type offset = int
[@@deriving show { with_path = false }]

type position = offset * offset
[@@deriving show { with_path = false }]

let warning position fmt =
  Format.eprintf "Warning %a: " pp_position position;
  Format.kfprintf (fun ppf -> Format.pp_print_string ppf "\n")
    Format.err_formatter
    fmt

let error position fmt =
  Format.eprintf "Error %a: " pp_position position;
  Format.kfprintf (fun ppf -> Format.pp_print_string ppf "\n")
    Format.err_formatter
    fmt
