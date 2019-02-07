open Source

(* ----- UNIFICATION USING Martelli & Montanari ALGORITHM ----- *)

type vartype = int

type typ_term = 
  | TyVar of vartype
  | TyConstant of type_constant
  | TyArrow of typ_term * typ_term
  | TyPair of typ_term * typ_term

type typ_constr = Eq of typ_term * typ_term

module Subst = Map.Make(struct type t = vartype let compare = compare end)
module VarSet = Set.Make(struct type t = vartype let compare = compare end)
module ConstrSet = Set.Make(struct type t = typ_constr let compare = compare end)

let rec vars_in_tt tt =
  match tt with
  | TyVar v -> VarSet.singleton v
  | TyConstant _ -> VarSet.empty
  | TyPair (tt1,tt2) | TyArrow (tt1,tt2) -> VarSet.union (vars_in_tt tt1) (vars_in_tt tt2)

let vars_in_constr constr =
  match constr with
  | Eq (tt1,tt2) -> VarSet.union (vars_in_tt tt1) (vars_in_tt tt2)

let rec tt_contains_var v tt =
  match tt with
  | TyVar v' when v=v' -> true
  | TyVar _ | TyConstant _ -> false
  | TyArrow (tt1,tt2) | TyPair (tt1,tt2) -> (tt_contains_var v tt1) || (tt_contains_var v tt2)

let rec constr_contains_var v constr =
  match constr with
  | Eq (tt1,tt2) -> (tt_contains_var v tt1) || (tt_contains_var v tt2)

let tt_conflict tt1 tt2 =
  match tt1,tt2 with
  | _, TyVar _ | TyVar _, _ -> false
  | TyConstant c1, TyConstant c2 -> c1 <> c2
  | TyPair _, TyPair _ | TyArrow _, TyArrow _ -> false
  | _ -> true

let tt_occurs_check_fail tt1 tt2 =
  match tt1,tt2 with
  | _, TyVar _ -> false
  | TyVar v, tt -> tt_contains_var v tt
  | _, _ -> false

let rec substitute_tt v tt tt_src =
  match tt_src with
  | TyVar v' when v = v' -> tt
  | TyVar v' -> TyVar v'
  | TyPair (a,b) -> TyPair (substitute_tt v tt a, substitute_tt v tt b)
  | TyArrow (a,b) -> TyArrow (substitute_tt v tt a, substitute_tt v tt b)
  | TyConstant c -> TyConstant c

let substitute_constr v tt constr =
  match constr with
  | Eq (tt1, tt2) -> Eq (substitute_tt v tt tt1, substitute_tt v tt tt2)

let eqs_splittable tt1 tt2 =
match tt1, tt2 with
| TyPair _, TyPair _ | TyArrow _, TyArrow _ -> true
| _ -> false

let split_eqs tt1 tt2 =
  match tt1, tt2 with
  | TyPair (a,b), TyPair (c,d) | TyArrow (a,b), TyArrow (c,d) ->
    [ Eq (a,c) ; Eq (b,d) ]
  | _ -> assert false

exception NoSolution
exception Simplified of ConstrSet.t
exception NothingDone of ConstrSet.t

let simplify_constraints cs =
  let rec simplify cs c =
    match c with
    | Eq (t,t') when tt_conflict t t'          -> raise NoSolution
    | Eq (t,t') when tt_occurs_check_fail t t' -> raise NoSolution
    | Eq (t,t') when t=t' -> (* Remove *)
      let cs = ConstrSet.remove c cs in
      raise (Simplified cs)
    | Eq (t,t') when eqs_splittable t t' -> (* Decompose *)
      let cs = ConstrSet.remove c cs in
      let cs = ConstrSet.union (ConstrSet.of_list (split_eqs t t')) cs in
      raise (Simplified cs)
    | Eq (t, TyVar v) when (match t with TyVar _ -> false | _ -> true) -> (* Swap *)
      let cs = ConstrSet.remove c cs in
      let cs = ConstrSet.add (Eq (TyVar v, t)) cs in
      raise (Simplified cs)
    | Eq (TyVar v, t) when not (tt_contains_var v t) -> (* Eliminate *)
      if ConstrSet.exists (constr_contains_var v) (ConstrSet.remove c cs)
      then (
        let cs = ConstrSet.map (substitute_constr v t) cs in
        raise (Simplified cs)
      )
    | _ -> ()
  in
  try (
    ConstrSet.iter (simplify cs) cs ;
    raise (NothingDone cs)
  ) with Simplified cs -> cs

let rec unify cs =
  try unify (simplify_constraints cs)
  with NothingDone cs -> cs

let rec typ_term_to_typ subst typ =
  failwith "TODO"
