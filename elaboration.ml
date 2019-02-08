open Source

(* ----- UNIFICATION ----- *)

type typ_term = 
  | TtVar of vartype
  | TtConstant of type_constant
  | TtArrow of typ_term * typ_term
  | TtPair of typ_term * typ_term

type typ_constr = Eq of typ_term * typ_term

(* Substitutions *)

module Subst = Map.Make(struct type t = vartype let compare = compare end)

let id_subst = Subst.empty

let singleton v k = Subst.singleton v k

let substitute_var s v =
  if Subst.mem v s
  then Subst.find v s
  else TtVar v

let rec substitute_tt s tt =
  match tt with
  | TtVar v -> substitute_var s v
  | TtPair (a,b) -> TtPair (substitute_tt s a, substitute_tt s b)
  | TtArrow (a,b) -> TtArrow (substitute_tt s a, substitute_tt s b)
  | TtConstant c -> TtConstant c

let compose_subst s1 s2 =
  let compose_with acc (v,tt) =
    Subst.add v (substitute_tt s1 tt) acc
  in
  List.fold_left compose_with s1 (Subst.bindings s2)

(* Operations on type terms *)

module VarSet = Set.Make(struct type t = vartype let compare = compare end)

let rec vars_in_tt tt =
  match tt with
  | TtVar v -> VarSet.singleton v
  | TtConstant _ -> VarSet.empty
  | TtPair (tt1,tt2) | TtArrow (tt1,tt2) -> VarSet.union (vars_in_tt tt1) (vars_in_tt tt2)

let vars_in_constr constr =
  match constr with
  | Eq (tt1,tt2) -> VarSet.union (vars_in_tt tt1) (vars_in_tt tt2)

let rec tt_contains_var v tt =
  match tt with
  | TtVar v' when v=v' -> true
  | TtVar _ | TtConstant _ -> false
  | TtArrow (tt1,tt2) | TtPair (tt1,tt2) -> (tt_contains_var v tt1) || (tt_contains_var v tt2)

let rec constr_contains_var v constr =
  match constr with
  | Eq (tt1,tt2) -> (tt_contains_var v tt1) || (tt_contains_var v tt2)

let tt_conflict tt1 tt2 =
  match tt1,tt2 with
  | _, TtVar _ | TtVar _, _ -> false
  | TtConstant c1, TtConstant c2 -> c1 <> c2
  | TtPair _, TtPair _ | TtArrow _, TtArrow _ -> false
  | _ -> true

let tt_occurs_check_fail tt1 tt2 =
  match tt1,tt2 with
  | _, TtVar _ -> false
  | TtVar v, tt -> tt_contains_var v tt
  | _, _ -> false

let substitute_constr s constr =
  match constr with
  | Eq (tt1, tt2) -> Eq (substitute_tt s tt1, substitute_tt s tt2)

let eqs_splittable tt1 tt2 =
match tt1, tt2 with
| TtPair _, TtPair _ | TtArrow _, TtArrow _ -> true
| _ -> false

let split_eqs tt1 tt2 =
  match tt1, tt2 with
  | TtPair (a,b), TtPair (c,d) | TtArrow (a,b), TtArrow (c,d) ->
    [ Eq (a,c) ; Eq (b,d) ]
  | _ -> assert false

(* Unification *)

exception NoSolution

let rec mgu cs =
  match cs with
  | [] -> id_subst
  | (Eq (t,t'))::_ when tt_conflict t t'          -> raise NoSolution         (* Conflict *)
  | (Eq (t,t'))::_ when tt_occurs_check_fail t t' -> raise NoSolution         (* Occurs check *)
  | (Eq (t,t'))::cs when t=t' ->                                              (* Remove *)
    mgu cs
  | (Eq (t,t'))::cs when eqs_splittable t t' ->                               (* Decompose *)
    mgu ((split_eqs t t')@cs)
  | (Eq (t, TtVar v))::cs when (match t with TtVar _ -> false | _ -> true) -> (* Swap *)
    mgu ((Eq (TtVar v, t))::cs)
  | (Eq (TtVar v, t))::cs when not (tt_contains_var v t) ->                   (* Eliminate *)
    let s = singleton v t in
    let cs = List.map (substitute_constr s) cs in
    compose_subst (mgu cs) s
  | _ -> assert false

(* ----- ELABORATION USING A KIND OF W-- ALGORITHM ----- *)

module IdMap = Typechecker.IdMap

let rec typ_to_typ_term t =
  match t with
  | TyConstant c -> TtConstant c
  | TyArrow (t1,t2) -> TtArrow (typ_to_typ_term t1, typ_to_typ_term t2)
  | TyPair (t1,t2) -> TtPair (typ_to_typ_term t1, typ_to_typ_term t2)

let rec closed_typ_term_to_typ tt =
  match tt with
  | TtVar _ -> assert false
  | TtConstant c -> TyConstant c
  | TtPair (tt1,tt2) -> TyPair (closed_typ_term_to_typ tt1, closed_typ_term_to_typ tt2)
  | TtArrow (tt1,tt2) -> TyArrow (closed_typ_term_to_typ tt1, closed_typ_term_to_typ tt2)

let substitute_env s env =
  IdMap.map (substitute_tt s) env

(*
Arguments:
  - [env] : The current environment, mapping variables to type term
  - [t] : A partially typed term

Output: (subst, type)
  - [subst] : A substitution that witnesses the returned type term [type].
  Type checking [t] using [env] composed with the substitution [subst] should give the type [type].
  - [type] : A type term for the term [t]
*)
let rec w env (t:untyped_term) =
  match t with
  | Var id -> (id_subst, IdMap.find id env)

  | App (t,u) ->
    let (u_subst, u_t) = w env u.value in
    let (t_subst, t_t) = w (substitute_env u_subst env) t.value in
    let final_vartype = fresh_vartype () in
    let mgu_subst = mgu [Eq (t_t, TtArrow (u_t, TtVar final_vartype))] in
    (compose_subst mgu_subst (compose_subst t_subst u_subst), substitute_var mgu_subst final_vartype)

  | Lam ((var_id, (typ_opt,typ_id)),t) ->

    let typ = begin match typ_opt with
      | None -> TtVar typ_id
      | Some typ -> typ_to_typ_term typ
    end in
    
    let env' = IdMap.add var_id typ env in
    let (subst, tt) = w env' t.value in
    (subst, TtArrow (substitute_tt subst typ, tt))

  | Pair (u,v) -> failwith "TODO"

  | Fst t -> failwith "TODO"

  | Snd t -> failwith "TODO"

  | Literal lit ->
    (id_subst, typ_to_typ_term (Typechecker.type_of_lit lit))

  | Primitive p ->
    (id_subst, typ_to_typ_term (Typechecker.type_of_prim p))


