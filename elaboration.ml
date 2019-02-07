open Source

(* ----- UNIFICATION USING Martelli & Montanari ALGORITHM ----- *)

type vartype = int

type typ_term = 
  | TyVar of vartype
  | TyConstant of type_constant
  | TyArrow of typ_term * typ_term
  | TyPair of typ_term * typ_term

type typ_constr = Eq of typ_term * typ_term

let rec tt_contains_var tt v =
    match tt with
    | TyVar v' when v=v' -> true
    | TyVar _ -> false
    | TyConstant _ -> false
    | TyArrow (tt1, tt2) | TyPair (tt1, tt2) ->
        (tt_contains_var tt1 v) || (tt_contains_var tt2 v)

let tt_conflict tt1 tt2 =
    match tt1,tt2 with
    | _, TyVar _ | TyVar _, _ -> false
    | TyConstant c1, TyConstant c2 -> c1 <> c2
    | TyPair _, TyPair _ | TyArrow _, TyArrow _ -> false
    | _ -> true

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

exception NoSolution

