
let (perimeter_: float -> float -> float) = fun (pi : float) -> fun (r : float) -> 2.0 * pi * r

let (perimeter: float -> float) = perimeter_ 3.14
