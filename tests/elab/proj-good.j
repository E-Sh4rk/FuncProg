let (dup : float -> float * float) = fun (x : float) -> (x,x)

let (id1 : float -> float) = fun (x : float) -> fst (dup x)
let (id2 : float -> float) = fun (x : float) -> snd (dup x)
