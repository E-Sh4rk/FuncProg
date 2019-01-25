open Target

type cat_term =
  | Identity of ok
  | Curry of ok * ok * ok * cat_term
  | UnCurry of ok * ok * ok * cat_term
  | Apply of ok * ok
  | Fork of ok * ok * ok * cat_term * cat_term
  | Exl of ok * ok
  | Exr of ok * ok
  | UnitArrow of ok * cat_term
  | It of ok
  | Compose of (ok * cat_term * ok) list
  | Literal of Source.literal
  | Primitive of Source.primitive

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    failwith "Student! This is your job!"
  else
    defs
