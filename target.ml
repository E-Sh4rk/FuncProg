type program = (Source.binding * t) list

and t =
  | App of t * t
  | Identity of ok
  | Curry of ok * ok * ok
  | UnCurry of ok * ok * ok
  | Apply of ok * ok
  | Fork of ok * ok * ok
  | Exl of ok * ok
  | Exr of ok * ok
  | UnitArrow of ok
  | It of ok
  | Compose of ok * ok * ok
  | Literal of Source.literal
  | Primitive of Source.primitive
and ok =
  | OkFloat
  | OkUnit
  | OkPair of ok * ok
  | OkArrow of ok * ok

let compose oka okb okc a1 a2 =
  App (App (Compose (oka, okb, okc), a1), a2)

let fork oka okb okc a1 a2 =
  App (App (Fork (oka, okb, okc), a1), a2)

let curry oka okb okc a =
  App (Curry (oka, okb, okc), a)

let uncurry oka okb okc a =
  App (UnCurry (oka, okb, okc), a)

let unit_arrow ok a =
  App (UnitArrow ok, a)
