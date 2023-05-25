def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

def drop_false_head? {n : Nat} : Vector Bool (n+1) → Option (Vector Bool n)
  | Vector.cons false z => some z
  | _ => none
