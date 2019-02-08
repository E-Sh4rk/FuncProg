open Source

(* ----- UNIFICATION USING Martelli & Montanari ALGORITHM ----- *)

type vartype = int

type typ_term = 
  | TtVar of vartype
  | TtConstant of type_constant
  | TtArrow of typ_term * typ_term
  | TtPair of typ_term * typ_term

type typ_constr = Eq of typ_term * typ_term

module Subst = Map.Make(struct type t = vartype let compare = compare end)
module VarSet = Set.Make(struct type t = vartype let compare = compare end)
module ConstrSet = Set.Make(struct type t = typ_constr let compare = compare end)

let fresh_var =
  let next = ref 0 in
  begin fun () -> 
    next := !next+1 ;
    !next - 1
  end

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

let rec substitute_tt v tt tt_src =
  match tt_src with
  | TtVar v' when v = v' -> tt
  | TtVar v' -> TtVar v'
  | TtPair (a,b) -> TtPair (substitute_tt v tt a, substitute_tt v tt b)
  | TtArrow (a,b) -> TtArrow (substitute_tt v tt a, substitute_tt v tt b)
  | TtConstant c -> TtConstant c

let substitute_constr v tt constr =
  match constr with
  | Eq (tt1, tt2) -> Eq (substitute_tt v tt tt1, substitute_tt v tt tt2)

let eqs_splittable tt1 tt2 =
match tt1, tt2 with
| TtPair _, TtPair _ | TtArrow _, TtArrow _ -> true
| _ -> false

let split_eqs tt1 tt2 =
  match tt1, tt2 with
  | TtPair (a,b), TtPair (c,d) | TtArrow (a,b), TtArrow (c,d) ->
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
    | Eq (t, TtVar v) when (match t with TtVar _ -> false | _ -> true) -> (* Swap *)
      let cs = ConstrSet.remove c cs in
      let cs = ConstrSet.add (Eq (TtVar v, t)) cs in
      raise (Simplified cs)
    | Eq (TtVar v, t) when not (tt_contains_var v t) -> (* Eliminate *)
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

let rec closed_typ_term_to_typ tt =
  match tt with
  | TtVar _ -> assert false
  | TtConstant c -> TyConstant c
  | TtPair (tt1,tt2) -> TyPair (closed_typ_term_to_typ tt1, closed_typ_term_to_typ tt2)
  | TtArrow (tt1,tt2) -> TyArrow (closed_typ_term_to_typ tt1, closed_typ_term_to_typ tt2)

(* ----- ELABORATION USING A KIND OF W-- ALGORITHM ----- *)

let rec w t = (* Returns (subst, type term) *)
  failwith "TODO"


