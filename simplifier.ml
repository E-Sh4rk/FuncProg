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

let rec target_to_cat_term (t:t) : cat_term =
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
    Curry (oka, okb, okc, target_to_cat_term a)
  | App ((UnCurry (oka, okb, okc)), a) ->
    UnCurry (oka, okb, okc, target_to_cat_term a)
  | App (App ((Fork (oka, okb, okc)), a1), a2) ->
    Fork (oka, okb, okc, target_to_cat_term a1, target_to_cat_term a2)
  | App (UnitArrow ok, a) ->
    UnitArrow (ok, target_to_cat_term a)
  (* Case of compose *)
  | App (App ((Compose (oka, okb, okc)), a1), a2) ->
    let t1 = target_to_cat_term a1 in
    let t2 = target_to_cat_term a2 in
    Compose [(okc,t1,okb) ; (okb,t2,oka)]
  | _ -> assert false

let rec cat_term_to_target (t:cat_term) : t =
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
    curry oka okb okc (cat_term_to_target a)
  | UnCurry (oka, okb, okc, a) ->
    uncurry oka okb okc (cat_term_to_target a)
  | Fork (oka, okb, okc, a, b) ->
    fork oka okb okc (cat_term_to_target a) (cat_term_to_target b)
  | UnitArrow (ok, a) ->
    unit_arrow ok (cat_term_to_target a)
  (* Case of compose *)
  | Compose lst ->
    let lst = List.map (fun (okb,a,oka) -> (okb,cat_term_to_target a,oka)) lst in
    let rec aux lst = match lst with
      | [(_, t, _)] -> t
      | ((okc, t1, okb')::(okb, t2, oka)::lst) when okb = okb' ->
        let comp = compose oka okb okc t1 t2 in
        aux ((okc,comp,oka)::lst)
      | _ -> assert false
    in
    aux lst

let rec map_cat_term f (t:cat_term) : cat_term =
  match t with
  | Identity ok -> f (Identity ok)
  | Curry (oka,okb,okc,a) -> f (Curry (oka,okb,okc,map_cat_term f a))
  | UnCurry (oka,okb,okc,a) -> f (UnCurry (oka,okb,okc,map_cat_term f a))
  | Apply (oka,okb) -> f (Apply (oka,okb))
  | Fork (oka,okb,okc,a1,a2) -> f (Fork (oka,okb,okc,map_cat_term f a1,map_cat_term f a2))
  | Exl (oka,okb) -> f (Exl (oka,okb))
  | Exr (oka,okb) -> f (Exr (oka,okb))
  | UnitArrow (ok,a) -> f (UnitArrow (ok,map_cat_term f a))
  | It ok -> f (It ok)
  | Compose lst ->
    let lst = List.map (fun (oka,t,okb) -> (oka,map_cat_term f t,okb)) lst in
    f (Compose lst)
  | Literal lit -> f (Literal lit)
  | Primitive prim -> f (Primitive prim)

let map_compose_cat_term f (t:cat_term) : cat_term =
  let simpl (t:cat_term) : cat_term =
    match t with
    | Compose lst -> Compose (f lst)
    | t -> t
  in
  map_cat_term simpl t

(* Flatten nested compositions so it is easier to reason modulo associativity. *)
let normalize_cat_term (t:cat_term) : cat_term =
  let simpl lst =
    let lst = List.map (function (oka,Compose lst,okb) -> lst | a -> [a]) lst in
    List.flatten lst
  in
  map_compose_cat_term simpl t

let simplify_id (t:cat_term) : cat_term =
  let simpl lst =
    let lst' = List.filter (function (_,Identity _,_) -> false | _ -> true) lst in
    if List.length lst' = 0 then [List.hd lst] (* Empty compositions are not allowed *) else lst'
  in
  map_compose_cat_term simpl (normalize_cat_term t)

let simplify_apply_curry (t:cat_term) : cat_term =
  let rec simpl lst =
    match lst with
    | [] -> []
    | (_, Apply _, _)::(_, Fork (ok_t1_t2_in, _, ok_t2_out, Curry (ok_f_in1,ok_f_in2,ok_f_out,f), t2), ok_fork_in)::lst ->
      let t1 = Identity ok_t1_t2_in in
      let ok_f_in = OkPair(ok_f_in1,ok_f_in2) in
      simpl ((ok_f_out,f,ok_f_in)::(ok_f_in,Fork(ok_t1_t2_in,ok_t1_t2_in,ok_t2_out,t1,t2),ok_fork_in)::lst)
    | (_, Apply _, _)::(_, Fork (ok_t1_t2_in, _, ok_t2_out, Compose ((_,Curry (ok_f_in1,ok_f_in2,ok_f_out,f),ok_t1_out)::lst'), t2), ok_fork_in)::lst ->
      let t1 = if List.length lst' = 0
        then Identity ok_t1_out
        else Compose lst' in
      let ok_f_in = OkPair(ok_f_in1,ok_f_in2) in
      simpl ((ok_f_out,f,ok_f_in)::(ok_f_in,Fork(ok_t1_t2_in,ok_t1_out,ok_t2_out,t1,t2),ok_fork_in)::lst)
    | a::lst -> a::(simpl lst)
  in
  map_compose_cat_term simpl (normalize_cat_term t)

let simplify_proj (t:cat_term) : cat_term =
  let rec simpl lst =
    match lst with
    | [] -> []
    | (_, Exl _, _)::(_, Fork (oka, okb, _, f, _), _)::lst -> simpl ((okb,f,oka)::lst)
    | (_, Exr _, _)::(_, Fork (oka, _, okb, _, g), _)::lst -> simpl ((okb,g,oka)::lst)
    | a::lst -> a::(simpl lst)
  in
  map_compose_cat_term simpl (normalize_cat_term t)

(*let test_valid_cat_term (t:cat_term) : cat_term =
  let simpl lst =
    match lst with
    | [] -> assert false
    | lst ->
      if List.exists (function (_,Compose _,_) -> true | _ -> false) lst
      then assert false
      else lst
  in
  map_compose_cat_term simpl t*)

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    let simplify (b,t) =
      let ct = target_to_cat_term t in
      let ct = simplify_id ct in
      let ct = simplify_apply_curry ct in
      let ct = simplify_proj ct in

      let ct = simplify_id ct in
      let ct = simplify_apply_curry ct in
      let ct = simplify_proj ct in

      let ct = simplify_id ct in
      let ct = simplify_apply_curry ct in
      let ct = simplify_proj ct in

      let ct = simplify_id ct in
      let ct = simplify_apply_curry ct in
      let ct = simplify_proj ct in

      let ct = simplify_id ct in
      let ct = simplify_apply_curry ct in
      let ct = simplify_proj ct in

      (b, cat_term_to_target ct)
    in
    List.map simplify defs
  else
    defs
