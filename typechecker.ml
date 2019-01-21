open PPrint
open Source


(** [type_error pos msg] reports a type error and exits. *)
let type_error pos msg =
  Printf.eprintf "%s:\n%s\n"
    (Position.string_of_pos pos)
    msg;
  exit 1

(** [string_of_type ty] returns a human readable representation of a type. *)
let string_of_type t =
  let rec ty = function
    | TyConstant TyFloat ->
       string "float"
    | TyArrow (input, output) ->
       group (mayparen_ty_under_arrow_lhs input) ^^ break 1
       ^^ string "->"
       ^^ break 1 ^^ (group (ty output))
    | TyPair (lhs, rhs) ->
       group (mayparen_ty_under_pair_lhs lhs) ^^ break 1
       ^^ string "* " ^^ group (mayparen_ty_under_pair_rhs rhs)
    and mayparen_ty_under_arrow_lhs = function
      | (TyArrow _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
    and mayparen_ty_under_pair_lhs = function
      | (TyArrow _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
    and mayparen_ty_under_pair_rhs = function
      | (TyArrow _ | TyPair _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
  in
  let b = Buffer.create 13 in
  PPrintEngine.ToBuffer.pretty 0.8 80 b (group (ty t));
  Buffer.contents b

module IdMap = Map.Make(struct type t = identifier let compare = compare end)

let rec type_of_term (env:typ IdMap.t) (term_loc:term' Position.located) : typ =
   let pos = term_loc.position in
   let term = term_loc.value in
   match term with
   | Var id ->
      if IdMap.mem id env then IdMap.find id env
      else type_error pos "Identifier never declared."

   | App (t1, t2) ->
      begin match type_of_term env t1 with
      | TyConstant _ -> type_error pos "Bad application: left term is a constant."
      | TyArrow (typ1,typ1') ->
         if type_of_term env t2 = typ1
         then typ1'
         else type_error pos "Bad application: wrong argument type."
      | TyPair _ -> type_error pos "Bad application: left term is a pair."
      end

   | Lam ((id,typ), t) ->
      let env = IdMap.add id typ env in
      let typ' = type_of_term env t in
      TyArrow (typ, typ')

   | Pair (t1, t2) ->
      let typ1 = type_of_term env t1 in
      let typ2 = type_of_term env t2 in
      TyPair (typ1, typ2)

   | Fst t ->
      begin match type_of_term env t with
      | TyConstant _ -> type_error pos "Bad projection: term is a constant."
      | TyArrow _ -> type_error pos "Bad projection: term is a function."
      | TyPair (typ1,_) -> typ1
      end

   | Snd t ->
      begin match type_of_term env t with
      | TyConstant _ -> type_error pos "Bad projection: term is a constant."
      | TyArrow _ -> type_error pos "Bad projection: term is a function."
      | TyPair (_,typ2) -> typ2
      end

   | Literal lit -> TyConstant TyFloat

   | Primitive prim ->
      begin match prim with
      | Sin | Cos | Exp | Inv | Neg -> TyArrow (TyConstant TyFloat, TyConstant TyFloat)
      | Add | Mul -> (* According to the parser, it seems to be in curried form. *)
         TyArrow (TyConstant TyFloat, TyArrow (TyConstant TyFloat, TyConstant TyFloat))
      end

(** [check_program source] returns [source] if it is well-typed or
   reports an error if it is not. *)
let check_program (source : program_with_locations) : program_with_locations =
   (* Build the global environment *)
   let add_binding acc (binding_loc, _) =
      let (id,typ) = binding_loc.Position.value in
      if IdMap.mem id acc
      then type_error binding_loc.Position.position "Global identifier already defined!"
      else IdMap.add id typ acc
   in
   let env = List.fold_left add_binding IdMap.empty source in
   (* Check all definitions *)
   let check_def (binding_loc, term_loc) =
      let (_,typ) = binding_loc.Position.value in
      if type_of_term env term_loc <> typ
      then type_error binding_loc.Position.position "Declared type and actual type mismatch!"
   in
   List.iter check_def source ; source

module IdSet = Set.Make(struct type t = identifier let compare = compare end)

(** [eta_expanse source] makes sure that only functions are defined at
    toplevel and turns them into eta-long forms if needed. *)
let eta_expanse : program_with_locations -> program_with_locations =
   fun source ->
      let eta_expanse_if_necessary (binding_loc, t_loc) =
         let (_,typ) = binding_loc.Position.value in
         match typ with
         | TyArrow (typ, _) ->
            let pos = t_loc.Position.position in
            let term = t_loc.Position.value in
            let new_t_loc =
               begin match term with
               | Lam _ -> t_loc
               | t ->
                  let new_id = Id "__x__" in
                  let var_loc = { Position.position = pos; Position.value = Var new_id } in
                  let app_loc = { Position.position = pos; Position.value = App (t_loc, var_loc) } in
                  { Position.position = pos; Position.value = Lam ((new_id,typ), app_loc) }
               end
            in
            (binding_loc, new_t_loc)
            
         | TyPair _ | TyConstant _ ->
            type_error binding_loc.Position.position "Non-arrow toplevel definitions are not allowed!"
      in
      List.map eta_expanse_if_necessary source   

(** [expanse_toplevel_non_arrow source] expanse every toplevel constants (definitions with a non-arrow type) so that they become functions. *)
let expanse_toplevel_constants : program_with_locations -> program_with_locations =
   fun source ->
      (* Update the toplevel defitions *)
      let expansed = ref IdSet.empty in
      let expanse_if_necessary (binding_loc, t_loc) =
         let (id,typ) = binding_loc.Position.value in
         match typ with
         | TyArrow _ -> (binding_loc, t_loc)
         | TyPair _ | TyConstant _ ->
            expansed := IdSet.add id !expansed ;
            let new_t = Lam ((Id "_", TyConstant TyFloat), t_loc) in
            let new_t_loc = { t_loc with Position.value = new_t } in
            let new_binding = (id, TyArrow (TyConstant TyFloat,typ)) in
            let new_binding_loc = { binding_loc with Position.value = new_binding } in
            (new_binding_loc, new_t_loc)
      in
      let source = List.map expanse_if_necessary source in     
      (* Update the call to these definitions *)
      (* We can't directly use Source.map because it does not handle local environments *)
      let rec expanse_calls_to (ids:IdSet.t) (term_loc:term' Position.located) : (term' Position.located) =
         let pos = term_loc.position in
         let term = term_loc.value in
         let new_term = match term with
            | App (t1, t2) -> App (expanse_calls_to ids t1, expanse_calls_to ids t2)
            | Lam ((id,typ), t) ->
               let ids = IdSet.remove id ids in
               Lam ((id,typ), expanse_calls_to ids t)
            | Pair (t1, t2) -> Pair (expanse_calls_to ids t1, expanse_calls_to ids t2)
            | Fst t -> Fst (expanse_calls_to ids t)
            | Snd t -> Snd (expanse_calls_to ids t)
            | Var id ->
               if IdSet.mem id ids
               then
                  let cst_loc = { Position.position = pos; Position.value = Literal (Float 0.) } in
                  App (term_loc, cst_loc)
               else Var id
            | Literal l -> Literal l
            | Primitive p -> Primitive p
         in
         { Position.position = pos; Position.value = new_term }
      in
      let expanse_def (binding_loc, term_loc) =
         (binding_loc, expanse_calls_to !expansed term_loc)
      in
      List.map expanse_def source

let program : program_with_locations -> program_with_locations = fun source ->
  let xsource = check_program source in
  if !Options.typecheck_only then exit 0;
  eta_expanse (expanse_toplevel_constants xsource)
