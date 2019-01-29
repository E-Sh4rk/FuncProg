open Target

type cat_term =
  | Identity of ok
  | Curry of ok * ok * ok * cat_term
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
  | Apply _ -> "Apply"
  | Fork (_,_,_,t1,t2) -> Printf.sprintf "(%s) Δ (%s)" (*"Fork(%s,%s)"*) (string_of_cat_term t1) (string_of_cat_term t2)
  | Exl _ -> "Exl"
  | Exr _ -> "Exr"
  | UnitArrow (_,t) -> Printf.sprintf "UnitArrow(%s)" (string_of_cat_term t)
  | It _ -> "It"
  | Compose (a,b,c) -> string_of_compose (a,b,c)
  | Literal l -> Source.string_of_literal l
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
    failwith "UnCurry is not supported by the simplifier."
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

let make_compose lst =
  let (ok_out, _, _) = List.hd lst in
  let (_, _, ok_in) = List.nth lst ((List.length lst)-1) in
  Compose (ok_in,ok_out,lst)

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

let simplify_terms (t:cat_term) : cat_term =
  let simpl t =
    match t with
    (* exl Δ exr -> id *)
    | Fork (ok_in,_,_,Exl _, Exr _) -> Identity ok_in
    (* curry(apply) -> id *)
    | Curry (_,_,ok_out,Apply _) -> Identity ok_out
    | t -> t
  in
  map_cat_term simpl (normalize_cat_term t)

let simplify_compositions (t:cat_term) : cat_term =
  let rec simpl lst =
    match lst with
    | [] -> []
    (* f . id -> f *)
    | (f_out, f, f_in)::(_, Identity _, _)::lst -> simpl ((f_out, f, f_in)::lst)
    (* id . g -> g *)
    | (_, Identity _, _)::(g_out, g, g_in)::lst -> simpl ((g_out, g, g_in)::lst)
    (* it . f -> it *)
    | (it_out, It _, _)::(_, f, f_in)::lst -> simpl ((it_out, It f_in, f_in)::lst)
    (* exl . (f Δ g) -> f *)
    | (_, Exl _, _)::(_, Fork (oka, okb, _, f, _), _)::lst -> simpl ((okb,f,oka)::lst)
    (* exr . (f Δ g) -> g *)
    | (_, Exr _, _)::(_, Fork (oka, _, okb, _, g), _)::lst -> simpl ((okb,g,oka)::lst)
    (* apply . ( (curry f) Δ t ) -> f . (Id Δ t) *)
    | (_, Apply _, _)::(_, Fork (ok_t1_t2_in, _, ok_t2_out, Curry (ok_f_in1,ok_f_in2,ok_f_out,f), t2), ok_fork_in)::lst ->
      let t1 = Identity ok_t1_t2_in in
      let ok_f_in = OkPair(ok_f_in1,ok_f_in2) in
      simpl ((ok_f_out,f,ok_f_in)::(ok_f_in,Fork(ok_t1_t2_in,ok_t1_t2_in,ok_t2_out,t1,t2),ok_fork_in)::lst)
    (* apply . ( ((curry f) . t1) Δ t2 ) -> f . (t1 Δ t2) *)
    | (_, Apply _, _)::(_, Fork (ok_t1_t2_in, _, ok_t2_out, Compose (ok_t1_in,_,(_,Curry (ok_f_in1,ok_f_in2,ok_f_out,f),ok_t1_out)::lst'), t2), ok_fork_in)::lst ->
      let t1 = Compose (ok_t1_in,ok_t1_out,lst') in
      let ok_f_in = OkPair(ok_f_in1,ok_f_in2) in
      simpl ((ok_f_out,f,ok_f_in)::(ok_f_in,Fork(ok_t1_t2_in,ok_t1_out,ok_t2_out,t1,t2),ok_fork_in)::lst)
    (* (u Δ v) . w  -> (u . w) Δ (v . w) *)
    | (ok_out,Fork(_,out_u,out_v,u,v),_)::(out_w,w,in_w)::lst ->
      simpl ((ok_out, Fork(in_w,out_u,out_v,make_compose [(out_u,u,out_w);(out_w,w,in_w)],make_compose [(out_v,v,out_w);(out_w,w,in_w)]),in_w)::lst)
    | a::lst -> a::(simpl lst)
  in
  map_compose_cat_term simpl (normalize_cat_term t)

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    let simplify (b,t) =
      let ct = target_to_cat_term t in

      let res = ref ct in
      let old_res = ref None in
      while !old_res <> (Some !res)
      do
        old_res := Some (!res) ;
        res := simplify_terms (!res) ;
        res := simplify_compositions (!res)
      done ;

      let ct = !res in
      (* Printf.printf "%s\n" (string_of_cat_term ct) ; flush_all () ; *)
      (b, cat_term_to_target ct)
    in
    List.map simplify defs
  else
    defs
