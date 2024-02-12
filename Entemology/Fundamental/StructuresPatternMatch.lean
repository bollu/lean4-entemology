inductive SomeType
  | someConstructor : Nat → SomeType

def SomeType.getN : SomeType → Nat
  | .someConstructor n => n

inductive DependentType (n : Nat)
  | mk : Fin n → DependentType n

structure SomeStruct where
  ty : SomeType
  depTy : DependentType ty.getN

def someFunction : SomeStruct → SomeStruct
  | struct => match struct.ty with
    |.someConstructor n =>
      have h : struct.ty.getN = n := by
        simp [SomeType.getN]
        rfl -- there seems to be no way of getting this to work
      let depTy : DependentType (n+1) := match struct.depTy with
        | .mk n => .mk <| h ▸ n.succ
      { ty := .someConstructor (n+1), depTy := depTy }
