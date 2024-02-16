inductive BoolRel : Bool → Bool → Prop
  | base : BoolRel true false
  | trans {x y z : Bool} : BoolRel x y → BoolRel y z → BoolRel x z

theorem BoolRel.irreflexive : forall x, ¬ (BoolRel x x) := by
  intro x hcontra
  induction hcontra
--   type mismatch when assigning motive
--   fun x x hcontra => False
-- has type
--   Bool → (x : Bool) → BoolRel x x → Prop : Type
-- but is expected to have type
--   (a a_1 : Bool) → BoolRel a a_1 → Prop : Type

-- more modern versions produce:

  -- target (or one of its indices) occurs more than once
  -- x

-- Could the elaborator do something like this?
--   suffices forall x y, x = y → ¬ (BoolRel x y) by
--     exact this x x rfl
--   intro x y hxy hcontra
--   induction hcontra
