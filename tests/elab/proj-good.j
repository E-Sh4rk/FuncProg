let dup = fun x -> (x,x)

let id1 = fun (x : float) -> fst (dup x)
let (id2 : float -> float) = fun x -> snd (dup x)
