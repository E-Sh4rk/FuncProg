
let (opp_double : float -> float) = fun (x : float) -> -(x * 2)

let (sin2 : float -> float) = sin

let (double_sin : float -> float) = fun (x : float) -> opp_double (sin2 x)