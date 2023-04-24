-- MutualTypeclass.lean:47:0: error: (kernel) declaration has free variables 'TypedUserSemantics.TSSA_TERMINATOR'
-- Lean (version 4.0.0-nightly-2023-03-31, commit 742d053a97bd, Release)


class TypeSemantics (Kind : Type) : Type 1 where
  toType : Kind → Type
  unit : Kind
  pair : Kind → Kind → Kind
  triple : Kind → Kind → Kind → Kind
  mkPair : ∀ {k1 k2 : Kind}, toType k1 → toType k2 → toType (pair k1 k2)
  fstPair : ∀ {k1 k2 : Kind}, toType (pair k1 k2) → toType k1
  sndPair : ∀ {k1 k2 : Kind}, toType (pair k1 k2) → toType k2
  mkTriple : ∀ {k1 k2 k3 : Kind}, toType k1 → toType k2 → toType k3 → toType (triple k1 k2 k3)
  fstTriple : ∀ {k1 k2 k3 : Kind}, toType (triple k1 k2 k3) → toType k1
  sndTriple : ∀ {k1 k2 k3 : Kind}, toType (triple k1 k2 k3) → toType k2
  trdTriple : ∀ {k1 k2 k3 : Kind}, toType (triple k1 k2 k3) → toType k3

inductive KindExpr (Kind : Type) : Type
  | ofKind : Kind → KindExpr Kind
  | unit : KindExpr Kind
  | pair : KindExpr Kind → KindExpr Kind → KindExpr Kind
  | triple : KindExpr Kind → KindExpr Kind → KindExpr Kind → KindExpr Kind



open TypeSemantics

class TypedUserSemantics (Op : Type) (Kind : Type) [TypeSemantics Kind] where
  argKind : Op → Kind
  rgnDom : Op → Kind
  rgnCod : Op → Kind
  outKind : Op → Kind
  eval : ∀ (o : Op), toType (argKind o) → (toType (rgnDom o) →
    toType (rgnCod o)) → toType (outKind o)


namespace TypedUserSemantics

inductive Context (Kind : Type) where
  | empty : Context Kind
  | push : Context Kind → Var → Kind → Context Kind

inductive CVar {Kind : Type} : Context Kind → Kind → Type where
  | here : ∀ {Γ : Context Kind} {k : Kind}, CVar (Γ.push v k) k
  | there : ∀ {Γ : Context Kind} {k₁ k₂ : Kind} {v : Var}, CVar Γ k₁ → CVar (Γ.push v k₂) k₁

-- set_option hygiene false in
-- set_option tactic.hygienic false
mutual

inductive TSSA_STMT (Op : Type) {Kind : Type} [h : TypeSemantics Kind] [h' : TypedUserSemantics Op Kind] :
    (Γ : Context Kind) → (Γr : Context (Kind × Kind)) → Context Kind → Type where
  /-- lhs := rhs; rest of the program -/
  | assign {k : Kind} (lhs : Var) (rhs : TSSA_EXPR Op Γ Γr k)
      (rest : TSSA_STMT Op (Γ.push lhs k) Γr Γ') : @TSSA_STMT Op _ h h' Γ Γr (Γ'.push lhs k)
  /-- no operation. -/
  | nop : TSSA_STMT Op Γ Γr Context.empty
  /-- above; ret v -/

inductive TSSA_TERMINATOR (Op : Type) {Kind : Type} [h : TypeSemantics Kind] [h' : TypedUserSemantics Op Kind]:
    (Γ : Context Kind) → (Γr : Context (Kind × Kind)) → Kind → Type where
  /-- above; ret v -/
  | ret {k : Kind} (above : TSSA_STMT Op Γ Γr Γ') (v : CVar Γ' k) : @TSSA_TERMINATOR Op _ h h' Γ Γr k

inductive TSSA_EXPR (Op : Type) {Kind : Type} [h : TypeSemantics Kind] [h' : TypedUserSemantics Op Kind] :
    (Γ : Context Kind) → (Γr : Context (Kind × Kind)) → Kind → Type where
  /-- (fst, snd) -/
  | pair (fst : CVar Γ k₁) (snd : CVar Γ k₂) : TSSA_EXPR Op Γ Γr (pair k₁ k₂)
  /-- (fst, snd, third) -/
  | triple (fst : CVar Γ k₁) (snd : CVar Γ k₂) (third : CVar Γ k₃) : TSSA_EXPR Op Γ Γr (triple k₁ k₂ k₃)
  /-- op (arg) { rgn } rgn is an argument to the operation -/
  | op (o : Op) (arg : CVar Γ (argKind o)) (rgn : @TSSA_REGION Op _ h h' Γ Γr (rgnDom o) (rgnCod o)) :
      TSSA_EXPR Op Γ Γr (outKind o)
  /-- a variable. -/
  | var (v : CVar Γ k) : TSSA_EXPR Op Γ Γr k

inductive TSSA_REGION (Op : Type) {Kind : Type} [h : TypeSemantics Kind] [h' : TypedUserSemantics Op Kind] :
    (Γ : Context Kind) → (Γr : Context (Kind × Kind)) → Kind → Kind → Type where
  /- fun arg => body -/
  | rgn {arg : Var} {dom cod : Kind} (body : @TSSA_TERMINATOR Op _ h h' (Γ.push arg dom) Γr cod) :
      TSSA_REGION Op Γ Γr dom cod
  /- no function / non-existence of region. -/
  | rgn0 : TSSA_REGION Op Γ Γr unit unit
  /- a region variable. --/
  | rgnvar (v : CVar Γr (k₁, k₂)) : TSSA_REGION Op Γ Γr k₁ k₂

end
