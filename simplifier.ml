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
  | Compose of (ok * cat_term * ok) list (* ok_codomain, morphism, ok_domain *)
  | Literal of Source.literal
  | Primitive of Source.primitive

let rec target_to_simple_term (t:t) : cat_term =
  match t with
  (* Base cases *)
  | Identity ok -> Identity ok
  | Apply (ok1, ok2) -> Apply (ok1, ok2)
  | Exl (ok1, ok2) -> Exl (ok1, ok2)
  | Exr (ok1, ok2) -> Exr (ok1, ok2)
  | It ok -> It ok
  | Literal l -> Literal l
  | Primitive p -> Primitive p
  (* Inductive cases *)
  | App ((Curry (oka, okb, okc)), a) ->
    Curry (oka, okb, okc, target_to_simple_term a)
  | App ((UnCurry (oka, okb, okc)), a) ->
    UnCurry (oka, okb, okc, target_to_simple_term a)
  | App (App ((Fork (oka, okb, okc)), a1), a2) ->
    Fork (oka, okb, okc, target_to_simple_term a1, target_to_simple_term a2)
  | App (UnitArrow ok, a) ->
    UnitArrow (ok, target_to_simple_term a)
  (* Case of compose *)
  | App (App ((Compose (oka, okb, okc)), a1), a2) ->
    let t1 = target_to_simple_term a1 in
    let t2 = target_to_simple_term a2 in
    let chain_left =
    begin match t1 with
      | Compose chain -> chain
      | t1 -> [okc,t1,okb]
    end in
    let chain_right =
    begin match t2 with
      | Compose chain -> chain
      | t2 -> [okb,t2,oka]
    end in
    Compose (chain_left@chain_right)
  | _ -> assert false

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    failwith "Student! This is your job!"
  else
    defs
