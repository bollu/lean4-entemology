inductive Ty where
| star: Ty
notation " ✶ " => Ty.star

abbrev Context : Type := List Ty

inductive Lookup : Context → Ty → Type where
| z : Lookup (t :: Γ) t

inductive Term : Context → Ty → Type where
| var : Lookup Γ a → Term Γ a
| lam : Term (✶ :: Γ) ✶ → Term Γ ✶
| ap : Term Γ ✶ → Term Γ ✶ → Term Γ ✶

abbrev plus : Term Γ a → Term Γ a
| .var i => .var i
| .lam n => .lam (plus n)
| .ap (.lam _) m => plus m -- This case takes precedence over the next one.
| .ap l m => (plus l).ap (plus m)

example : plus (.ap l m) = (plus l).ap (plus m) := by
  unfold plus
  -- ^^ failed to generate equality theorems for `match` expression `plus.match_1`


