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
  | Compose of ok * ok * ((ok * cat_term * ok) list) (* global_ok_domain, global_ok_codomain,[ok_codomain, morphism, ok_domain] *)
  | Literal of Source.literal
  | Primitive of Source.primitive

let rec string_of_compose (_,_,lst) =
  match lst with
  | [] -> ""
  | (_,hd,_)::lst ->
    let lst_str = List.fold_left (fun acc (_,t,_) -> Printf.sprintf "%s o %s" acc (string_of_cat_term t)) "" lst
    in Printf.sprintf "%s%s" (string_of_cat_term hd) lst_str

and string_of_cat_term (t:cat_term) : string =
  match t with
  | Identity _ -> "Id"
  | Curry (_,_,_,t) -> Printf.sprintf "Curry(%s)" (string_of_cat_term t)
  | UnCurry (_,_,_,t) -> Printf.sprintf "UnCurry(%s)" (string_of_cat_term t)
  | Apply _ -> "Apply"
  | Fork (_,_,_,t1,t2) -> Printf.sprintf (*"(%s Δ %s)"*) "Fork(%s,%s)" (string_of_cat_term t1) (string_of_cat_term t2)
  | Exl _ -> "Exl"
  | Exr _ -> "Exr"
  | UnitArrow (_,t) -> Printf.sprintf "UnitArrow(%s)" (string_of_cat_term t)
  | It _ -> "It"
  | Compose (a,b,c) -> string_of_compose (a,b,c)
  | Literal t -> Source.string_of_literal t
  | Primitive p -> Source.string_of_primitive p

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
    Compose (oka, okc, [(okc,t1,okb) ; (okb,t2,oka)])
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
  | Compose (ok_in, ok_out, []) when ok_in = ok_out -> Identity ok_in
  | Compose (_, _, lst) when List.length lst > 0 ->
    let lst = List.map (fun (okb,a,oka) -> (okb,cat_term_to_target a,oka)) lst in
    let rec aux lst = match lst with
      | [(_, t, _)] -> t
      | ((okc, t1, okb')::(okb, t2, oka)::lst) when okb = okb' ->
        let comp = compose oka okb okc t1 t2 in
        aux ((okc,comp,oka)::lst)
      | _ -> assert false
    in
    aux lst
  | Compose _ -> assert false

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
  | Compose (ok_in,ok_out,lst) ->
    let lst = List.map (fun (oka,t,okb) -> (oka,map_cat_term f t,okb)) lst in
    f (Compose (ok_in, ok_out, lst))
  | Literal lit -> f (Literal lit)
  | Primitive prim -> f (Primitive prim)

let map_compose_cat_term f (t:cat_term) : cat_term =
  let simpl (t:cat_term) : cat_term =
    match t with
    | Compose (ok_in, ok_out, lst) -> Compose (ok_in, ok_out, f lst)
    | t -> t
  in
  map_cat_term simpl t

(* Flatten nested compositions so it is easier to reason modulo associativity. *)
(* Also remove empty or one-element compositions. *)
let normalize_cat_term (t:cat_term) : cat_term =
  let rm_useless_compose (t:cat_term) : cat_term =
    match t with
    | Compose (ok_in, ok_out, []) when ok_in = ok_out -> Identity ok_in
    | Compose (ok_in, ok_out, [(ok_out',t,ok_in')]) when ok_in=ok_in' && ok_out=ok_out' -> t
    | Compose (ok_in, ok_out, lst) when List.length lst > 0 -> Compose (ok_in, ok_out, lst)
    | Compose _ -> assert false
    | t -> t
  in
  let merge_compose lst =
    let lst = List.map (function (oka,Compose (_,_,lst),okb) -> lst | a -> [a]) lst in
    List.flatten lst
  in
  map_compose_cat_term merge_compose (map_cat_term rm_useless_compose t)

let simplify_id (t:cat_term) : cat_term =
  let simpl lst =
    List.filter (function (_,Identity _,_) -> false | _ -> true) lst
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
    | (_, Apply _, _)::(_, Fork (ok_t1_t2_in, _, ok_t2_out, Compose (ok_t1_in,_,(_,Curry (ok_f_in1,ok_f_in2,ok_f_out,f),ok_t1_out)::lst'), t2), ok_fork_in)::lst ->
      let t1 = Compose (ok_t1_in,ok_t1_out,lst') in
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
  let simpl2 t =
    match t with
    | Fork (ok_a,_,_,Exl _, Exr _) -> Identity ok_a
    | t -> t
  in
  map_cat_term simpl2 (map_compose_cat_term simpl (normalize_cat_term t))

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
