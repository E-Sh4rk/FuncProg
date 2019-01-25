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

let rec simple_term_to_target (t:cat_term) : t =
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
  | Curry (oka, okb, okc, a) ->
    curry oka okb okc (simple_term_to_target a)
  | UnCurry (oka, okb, okc, a) ->
    uncurry oka okb okc (simple_term_to_target a)
  | Fork (oka, okb, okc, a, b) ->
    fork oka okb okc (simple_term_to_target a) (simple_term_to_target b)
  | UnitArrow (ok, a) ->
    unit_arrow ok (simple_term_to_target a)
  (* Case of compose *)
  | Compose lst ->
    let lst = List.map (fun (okb,a,oka) -> (okb,simple_term_to_target a,oka)) lst in
    let rec aux lst = match lst with
      | [(_, t, _)] -> t
      | ((okc, t1, okb')::(okb, t2, oka)::lst) when okb = okb' ->
        let comp = compose oka okb okc t1 t2 in
        aux ((okc,comp,oka)::lst)
      | _ -> assert false
    in
    aux lst

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    let simplify (b,t) =
      (b, simple_term_to_target (target_to_simple_term t))
    in
    List.map simplify defs
  else
    defs
