open Source
open Target
open Typechecker

module IdMap = Typechecker.IdMap
type ctx =
   | CtxEmpty
   | CtxSingleton of string * ok * typ
   | CtxProd of ctx * ctx * ok

let ok_of_ctx ctx =
   match ctx with
   | CtxEmpty -> OkUnit
   | CtxSingleton (_,ok,_) -> ok
   | CtxProd (_,_,ok) -> ok

let rec compile_app (ctx:ctx) (u:term) (v:term) : (t * ok) =
   let (ta, oka) = compile_term ctx u in
   let (tb, okb) = compile_term ctx v in
   let ok_ctx = ok_of_ctx ctx in
   let oka' = match oka with OkArrow(_,oka') -> oka' | _ -> assert false in
   let frk = fork ok_ctx oka okb ta tb in
   let apl = Apply (okb, oka') in
   (compose ok_ctx (OkPair (oka, okb)) oka' apl frk, oka')

and compile_term (c:ctx) (t:term) : (t * ok) =
   failwith "Student! This is your job!"

(** [source_to_categories] translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
   failwith "Student! This is your job!"
