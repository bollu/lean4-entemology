def Float.isZero : Float -> Bool
  | 0 => true
  | _ => false
/-
dependent elimination failed, type mismatch when solving alternative with type
  motive (Float.ofScientific 0 false 0)
but expected
  motive x
-/
