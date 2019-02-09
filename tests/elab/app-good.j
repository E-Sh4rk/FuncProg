let (apply : (float -> float) -> float -> float) =
  fun f -> fun x -> f (x)