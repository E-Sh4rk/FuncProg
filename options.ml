let no_elaboration = ref false

let typecheck_only = ref false

let eta_expanse_only = ref false

let without_oks = ref false

let simplify = ref true

let compact = ref false

let options = Arg.([
  "--no-elaboration", Unit (fun () -> no_elaboration := true),
  " Do not elaborate. Terms must by type-annoted.";

  "--typecheck", Unit (fun () -> typecheck_only := true),
  " Typecheck and stop.";

  "--eta-expanse", Unit (fun () -> eta_expanse_only := true),
  " Typecheck, eta expanse and stop (for testing).";

  "--no-ok", Unit (fun () -> without_oks := true),
  " Do not produce 'ok' witnesses.";

  "--no-simplify", Unit (fun () -> simplify := false),
  " Do not apply the simplifier.";

  "--compact", Unit (fun () -> compact := true),
  " Compactify the generated OCaml code."

])

let source_file =
  ref ""

let msg = "joujou [options] source_file"

let get_source_file () =
  if !source_file = "" then (Arg.usage options msg; exit 1);
  !source_file

let target_file () =
  Filename.chop_extension (get_source_file ()) ^ ".ml"

let analyse =
  Arg.(parse (align options) ((:=) source_file) msg)
