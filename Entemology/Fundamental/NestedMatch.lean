inductive NumType | i32
  deriving Repr
  open NumType

abbrev FuncType := List NumType × List NumType
notation:56 lhs:55 " ->> " rhs:54 => (lhs, rhs)

inductive Code : FuncType -> Type where
| i32_add    :                     Code (i32 :: i32 :: L ->> i32 :: L)
| i32_const  : (const : UInt32) -> Code (              L ->> i32 :: L)
| seq        : Code (A ->> B) -> Code (B ->> C) -> Code (A ->> C)
  deriving Repr
  open Code
  infixl:54 "; " => Code.seq

inductive Stack : List NumType -> Type where
| bottom : Stack []
| val : UInt32 -> Stack Γ -> Stack (ty :: Γ)
  infixr:67 " :: " => Stack.val

structure Cfg (A B : List NumType) where
  stack : Stack A
  code  : Code (A ->> B)

def reduce (cfg : Cfg A B) : Stack B :=
  match h : cfg.code with
  | i32_const c; restcode =>
    have : sizeOf restcode < sizeOf cfg.code := by rewrite [h]; simp_arith
    reduce ⟨c :: cfg.stack, restcode⟩
  | i32_add; restcode =>
    let (x :: y :: rest) := cfg.stack
    have : sizeOf restcode < sizeOf cfg.code := by rewrite [h]; simp_arith
    reduce ⟨(x + y) :: rest, restcode⟩
  | _ => sorry
termination_by reduce cfg => sizeOf cfg.code
