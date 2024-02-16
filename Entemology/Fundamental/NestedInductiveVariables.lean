-- (kernel) invalid nested inductive datatype 'And', nested inductive datatypes parameters cannot contain local variables.
inductive Rel : Bool → Bool → Prop
  | base : Rel true false
  | trans {x y z : Bool} (hxy : Rel x y ∧ Rel y z) : Rel x z
