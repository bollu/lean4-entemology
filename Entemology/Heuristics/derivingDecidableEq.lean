inductive MyNewType {MyType : Type 0} [DecidableEq MyType] : Type where
  | wrapper : MyType -> MyNewType
  deriving DecidableEq
/-
synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  fun a b => inst a b
inferred
  inst¹
-/
