open Source
open Target
open Typechecker

module IdMap = Typechecker.IdMap
type ctx =
   | CtxEmpty
   | CtxSingleton of string * typ * ok (* Var name, var type, var ok *)
   | CtxProd of ctx * ctx * ok         (* Left child, right child, ok for this node *)

let ok_of_ctx ctx =
   match ctx with
   | CtxEmpty -> OkUnit
   | CtxSingleton (_,_,ok) -> ok
   | CtxProd (_,_,ok) -> ok

let ok_of_primitive prim =
   match prim with
   | Sin | Cos | Exp | Inv | Neg -> OkArrow (OkFloat, OkFloat)
   | Add | Mul -> OkArrow (OkFloat, OkArrow (OkFloat, OkFloat))

let rec ok_of_type typ =
   match typ with
   | TyConstant TyFloat -> OkFloat
   | TyArrow (typ1,typ2) -> OkArrow (ok_of_type typ1, ok_of_type typ2)
   | TyPair (typ1,typ2) -> OkPair (ok_of_type typ1, ok_of_type typ2)

let rec compile_app (ctx:ctx) (u:term) (v:term) : (t * ok) =
   let ok_ctx = ok_of_ctx ctx in
   let (ta, oka) = compile_term ctx u in
   let (tb, okb) = compile_term ctx v in
   let oka' = match oka with OkArrow(_,oka') -> oka' | _ -> assert false in
   let frk = fork ok_ctx oka okb ta tb in
   let apl = Apply (okb, oka') in
   (compose ok_ctx (OkPair (oka, okb)) oka' apl frk, oka')

and compile_const (ctx:ctx) (c:literal) : (t * ok) =
   let ok_ctx = ok_of_ctx ctx in
   let ua = unit_arrow OkFloat c in
   let it = It ok_ctx in
   (compose ok_ctx OkUnit OkFloat ua it, OkFloat)

and compile_fst (ctx:ctx) (u:term) : (t * ok) =
   let ok_ctx = ok_of_ctx ctx in
   let (t, ok) = compile_term ctx u in
   let (oka, okb) = match ok with OkPair (oka, okb) -> (oka, okb) | _ -> assert false in
   let exl = Exl (oka, okb) in
   (compose ok_ctx ok oka exl t, oka)

and compile_snd (ctx:ctx) (u:term) : (t * ok) =
   let ok_ctx = ok_of_ctx ctx in
   let (t, ok) = compile_term ctx u in
   let (oka, okb) = match ok with OkPair (oka, okb) -> (oka, okb) | _ -> assert false in
   let exr = Exr (oka, okb) in
   (compose ok_ctx ok okb exr t, okb)

and compile_pair (ctx:ctx) (u:term) (v:term) : (t * ok) =
   let ok_ctx = ok_of_ctx ctx in
   let (ta, oka) = compile_term ctx u in
   let (tb, okb) = compile_term ctx v in
   (fork ok_ctx oka okb ta tb, OkPair(oka, okb))

and compile_prim (ctx:ctx) (p:primitive) : (t * ok) =
   let ok_ctx = ok_of_ctx ctx in
   let ok_prim = ok_of_primitive p in
   let (prim, prim_oka, prim_okb) =
      match ok_prim with
      | OkArrow (oka, OkArrow(okb,okc)) -> (* Arity 2 *)
         (curry oka okb okc (Primitive p), oka, OkArrow(okb,okc))
      | OkArrow (oka, okb) -> (* Arity 1 *) (Primitive p, oka, okb)
      | _ -> assert false
   in
   let exr = Exr (OkUnit, prim_oka) in
   let prim_exr = compose (OkPair (OkUnit, prim_oka)) prim_oka prim_okb prim exr in
   let curried_prim_exr = curry OkUnit prim_oka prim_okb prim_exr in
   let it = It ok_ctx in
   (compose ok_ctx OkUnit ok_prim curried_prim_exr it, ok_prim)

and compile_term (c:ctx) (t:term) : (t * ok) =
   failwith "Student! This is your job!"

(** [source_to_categories] translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
   failwith "Student! This is your job!"
