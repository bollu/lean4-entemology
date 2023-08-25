inductive FloatEnvelope
  | mk : Float -> FloatEnvelope

def isZero : FloatEnvelope -> Bool
  | .mk 0 => true
  | _ => false

/-
dependent elimination failed, type mismatch when solving alternative with type
  motive (FloatEnvelope.mk (Float.ofScientific 0 false 0))
but expected
  motive (FloatEnvelope.mk a)
-/
