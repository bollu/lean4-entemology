inductive LengthIndexedList (α : Type u) : Nat → Type u where
   | nil : LengthIndexedList α 0
   | cons : α → LengthIndexedList α n → LengthIndexedList α (n + 1)

def patternMatch (w : Nat) (x : LengthIndexedList Bool w) : Int :=
  match w, x with
    | .succ n, .cons s _  =>
      let sign := if s = true then -1 else 1
      sign * n
    | _, _ => 0

def patternMatchRev (w : Nat) (x : LengthIndexedList Bool w) : Int :=
  match x, w with
    | .cons s _, .succ n  =>
      let sign := if s = true then -1 else 1
      sign * n
    | _, _ => 0
