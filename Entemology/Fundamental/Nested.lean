inductive Tree (τ : Type) : Type
| Leaf (val : τ) : Tree τ
| Branch : List (Tree τ) → Tree τ

/-
def Tree.map1 (f : σ → τ) : Tree σ → Tree τ
| .Leaf s => .Leaf (f s)
| .Branch ss => .Branch (List.map (Tree.map1 f) ss)
5:4:
fail to show termination for
  Tree.map
with errors
structural recursion cannot be used

failed to prove termination, use `termination_by` to specify a well-founded relation
-/

mutual
def List.map2 (f: σ → τ) : List (Tree σ) → List (Tree τ)
| .nil => .nil
| .cons t ts => .cons (Tree.map2 f t) (List.map2 f ts)

def Tree.map2 (f : σ → τ) : Tree σ → Tree τ
| .Leaf s => .Leaf (f s)
| .Branch ss => .Branch (List.map2 f ss)
end

#print Tree.map2 /- fun {σ τ} f x => List.map2._mutual f (PSum.inr x) -/
#print List.map2._mutual
/-
def List.map2._mutual : {σ τ : Type} →
  (σ → τ) → (_x : List (Tree σ) ⊕' Tree σ) → PSum.casesOn _x (fun _x => List (Tree τ)) fun _x => Tree τ :=
fun {σ τ} f =>
  WellFounded.fix
    (_ :
      WellFounded
        (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
            Prod.instWellFoundedRelationProd).1)
    fun _x a =>
    PSum.casesOn (motive := fun x =>
      ((y : List (Tree σ) ⊕' Tree σ) →
          (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
                  Prod.instWellFoundedRelationProd).1
              y x →
            PSum.casesOn y (fun _x => List (Tree τ)) fun _x => Tree τ) →
        PSum.casesOn x (fun _x => List (Tree τ)) fun _x => Tree τ)
      _x
      (fun x a =>
        (match (motive :=
            (x : List (Tree σ)) →
              ((y : List (Tree σ) ⊕' Tree σ) →
                  (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
                          Prod.instWellFoundedRelationProd).1
                      y (PSum.inl x) →
                    PSum.casesOn y (fun _x => List (Tree τ)) fun _x => Tree τ) →
                List (Tree τ))
            x with
          | [] => fun x => []
          | t :: ts => fun x =>
            x (PSum.inr t)
                (_ :
                  (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
                        Prod.instWellFoundedRelationProd).1
                    (PSum.inr t) (PSum.inl (t :: ts))) ::
              x (PSum.inl ts)
                (_ :
                  (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
                        Prod.instWellFoundedRelationProd).1
                    (PSum.inl ts) (PSum.inl (t :: ts))))
          a)
      (fun x a =>
        (match (motive :=
            (x : Tree σ) →
              ((y : List (Tree σ) ⊕' Tree σ) →
                  (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
                          Prod.instWellFoundedRelationProd).1
                      y (PSum.inr x) →
                    PSum.casesOn y (fun _x => List (Tree τ)) fun _x => Tree τ) →
                Tree τ)
            x with
          | Tree.Leaf s => fun x => Tree.Leaf (f s)
          | Tree.Branch ss => fun x =>
            Tree.Branch
              (x (PSum.inl ss)
                (_ :
                  (invImage (fun a => PSum.casesOn a (fun val => (sizeOf val, 0)) fun val => (sizeOf val, 1))
                        Prod.instWellFoundedRelationProd).1
                    (PSum.inl ss) (PSum.inr (Tree.Branch ss)))))
          a)
      a
-/
