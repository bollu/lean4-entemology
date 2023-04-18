mutual
inductive A (t : Type)
| Bs : List (B t) → A t
| a : t → A t

inductive B (t : Type)
| As : List (A t) → B t
| b : t → B t
end


mutual
def A.map (f : t → t) : A t → A t
| .a t => .a (f t)
| .Bs bsList =>
    .Bs (B.listMap f bsList)

def A.listMap (f : t → t) : List (A t) → List (A t)
| [] => []
| a :: as => (A.map f a) :: A.listMap f as

def B.listMap (f : t → t) : List (B t) → List (B t)
| [] => []
| b :: bs => (B.map f b) :: B.listMap f bs

def B.map (f : t → t) : B t → B t
| .b t => .b (f t)
| .As asList => .As (A.listMap f asList)
end
termination_by
  A.map f a => sizeOf a
  B.map f b => sizeOf b
  A.listMap f as => sizeOf as
  B.listMap f bs => sizeOf bs

/-
def A.map._mutual : {t : Type} →
  (t → t) →
    (_x : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
      PSum.casesOn _x (fun _x => A t) fun _x =>
        PSum.casesOn _x (fun _x => List (B t)) fun _x => PSum.casesOn _x (fun _x => B t) fun _x => List (A t) :=
fun {t} f =>
  WellFounded.fix
    (_ :
      WellFounded
        (invImage
            (fun a =>
              PSum.casesOn a (fun val => sizeOf val) fun val =>
                PSum.casesOn val (fun val => sizeOf val) fun val =>
                  PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
            instWellFoundedRelation).1)
    fun _x a =>
    PSum.casesOn (motive := fun x =>
      ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
          (invImage
                  (fun a =>
                    PSum.casesOn a (fun val => sizeOf val) fun val =>
                      PSum.casesOn val (fun val => sizeOf val) fun val =>
                        PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                  instWellFoundedRelation).1
              y x →
            PSum.casesOn y (fun _x => A t) fun _x =>
              PSum.casesOn _x (fun _x => List (B t)) fun _x => PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
        PSum.casesOn x (fun _x => A t) fun _x =>
          PSum.casesOn _x (fun _x => List (B t)) fun _x => PSum.casesOn _x (fun _x => B t) fun _x => List (A t))
      _x
      (fun x a =>
        (match (motive :=
            (x : A t) →
              ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
                  (invImage
                          (fun a =>
                            PSum.casesOn a (fun val => sizeOf val) fun val =>
                              PSum.casesOn val (fun val => sizeOf val) fun val =>
                                PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                          instWellFoundedRelation).1
                      y (PSum.inl x) →
                    PSum.casesOn y (fun _x => A t) fun _x =>
                      PSum.casesOn _x (fun _x => List (B t)) fun _x =>
                        PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
                A t)
            x with
          | A.a t_1 => fun x => A.a (f t_1)
          | A.Bs bsList => fun x =>
            A.Bs
              (x (PSum.inr (PSum.inl bsList))
                (_ :
                  PSum.rec (fun val => sizeOf val)
                      (fun val =>
                        PSum.rec (fun val => sizeOf val)
                          (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                      (PSum.inl (A.Bs bsList)) >
                    PSum.rec (fun val => sizeOf val)
                      (fun val =>
                        PSum.rec (fun val => sizeOf val)
                          (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                      (PSum.inr (PSum.inl bsList)))))
          a)
      (fun val a =>
        PSum.casesOn (motive := fun x =>
          ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
              (invImage
                      (fun a =>
                        PSum.casesOn a (fun val => sizeOf val) fun val =>
                          PSum.casesOn val (fun val => sizeOf val) fun val =>
                            PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                      instWellFoundedRelation).1
                  y (PSum.inr x) →
                PSum.casesOn y (fun _x => A t) fun _x =>
                  PSum.casesOn _x (fun _x => List (B t)) fun _x =>
                    PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
            PSum.casesOn (PSum.inr x) (fun _x => A t) fun _x =>
              PSum.casesOn _x (fun _x => List (B t)) fun _x => PSum.casesOn _x (fun _x => B t) fun _x => List (A t))
          val
          (fun x a =>
            (match (motive :=
                (x : List (B t)) →
                  ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
                      (invImage
                              (fun a =>
                                PSum.casesOn a (fun val => sizeOf val) fun val =>
                                  PSum.casesOn val (fun val => sizeOf val) fun val =>
                                    PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                              instWellFoundedRelation).1
                          y (PSum.inr (PSum.inl x)) →
                        PSum.casesOn y (fun _x => A t) fun _x =>
                          PSum.casesOn _x (fun _x => List (B t)) fun _x =>
                            PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
                    List (B t))
                x with
              | [] => fun x => []
              | b :: bs => fun x =>
                x (PSum.inr (PSum.inr (PSum.inl b)))
                    (_ :
                      (invImage
                            (fun a =>
                              PSum.casesOn a (fun val => sizeOf val) fun val =>
                                PSum.casesOn val (fun val => sizeOf val) fun val =>
                                  PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                            instWellFoundedRelation).1
                        (PSum.inr (PSum.inr (PSum.inl b))) (PSum.inr (PSum.inl (b :: bs)))) ::
                  x (PSum.inr (PSum.inl bs))
                    (_ :
                      PSum.rec (fun val => sizeOf val)
                          (fun val =>
                            PSum.rec (fun val => sizeOf val)
                              (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                          (PSum.inr (PSum.inl (b :: bs))) >
                        PSum.rec (fun val => sizeOf val)
                          (fun val =>
                            PSum.rec (fun val => sizeOf val)
                              (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                          (PSum.inr (PSum.inl bs))))
              a)
          (fun val a =>
            PSum.casesOn (motive := fun x =>
              ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
                  (invImage
                          (fun a =>
                            PSum.casesOn a (fun val => sizeOf val) fun val =>
                              PSum.casesOn val (fun val => sizeOf val) fun val =>
                                PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                          instWellFoundedRelation).1
                      y (PSum.inr (PSum.inr x)) →
                    PSum.casesOn y (fun _x => A t) fun _x =>
                      PSum.casesOn _x (fun _x => List (B t)) fun _x =>
                        PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
                PSum.casesOn (PSum.inr (PSum.inr x)) (fun _x => A t) fun _x =>
                  PSum.casesOn _x (fun _x => List (B t)) fun _x => PSum.casesOn _x (fun _x => B t) fun _x => List (A t))
              val
              (fun x a =>
                (match (motive :=
                    (x : B t) →
                      ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
                          (invImage
                                  (fun a =>
                                    PSum.casesOn a (fun val => sizeOf val) fun val =>
                                      PSum.casesOn val (fun val => sizeOf val) fun val =>
                                        PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                                  instWellFoundedRelation).1
                              y (PSum.inr (PSum.inr (PSum.inl x))) →
                            PSum.casesOn y (fun _x => A t) fun _x =>
                              PSum.casesOn _x (fun _x => List (B t)) fun _x =>
                                PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
                        B t)
                    x with
                  | B.b t_1 => fun x => B.b (f t_1)
                  | B.As asList => fun x =>
                    B.As
                      (x (PSum.inr (PSum.inr (PSum.inr asList)))
                        (_ :
                          PSum.rec (fun val => sizeOf val)
                              (fun val =>
                                PSum.rec (fun val => sizeOf val)
                                  (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                              (PSum.inr (PSum.inr (PSum.inl (B.As asList)))) >
                            PSum.rec (fun val => sizeOf val)
                              (fun val =>
                                PSum.rec (fun val => sizeOf val)
                                  (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                              (PSum.inr (PSum.inr (PSum.inr asList))))))
                  a)
              (fun x a =>
                (match (motive :=
                    (x : List (A t)) →
                      ((y : A t ⊕' List (B t) ⊕' B t ⊕' List (A t)) →
                          (invImage
                                  (fun a =>
                                    PSum.casesOn a (fun val => sizeOf val) fun val =>
                                      PSum.casesOn val (fun val => sizeOf val) fun val =>
                                        PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                                  instWellFoundedRelation).1
                              y (PSum.inr (PSum.inr (PSum.inr x))) →
                            PSum.casesOn y (fun _x => A t) fun _x =>
                              PSum.casesOn _x (fun _x => List (B t)) fun _x =>
                                PSum.casesOn _x (fun _x => B t) fun _x => List (A t)) →
                        List (A t))
                    x with
                  | [] => fun x => []
                  | a :: as => fun x =>
                    x (PSum.inl a)
                        (_ :
                          (invImage
                                (fun a =>
                                  PSum.casesOn a (fun val => sizeOf val) fun val =>
                                    PSum.casesOn val (fun val => sizeOf val) fun val =>
                                      PSum.casesOn val (fun val => sizeOf val) fun val => sizeOf val)
                                instWellFoundedRelation).1
                            (PSum.inl a) (PSum.inr (PSum.inr (PSum.inr (a :: as))))) ::
                      x (PSum.inr (PSum.inr (PSum.inr as)))
                        (_ :
                          PSum.rec (fun val => sizeOf val)
                              (fun val =>
                                PSum.rec (fun val => sizeOf val)
                                  (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                              (PSum.inr (PSum.inr (PSum.inr (a :: as)))) >
                            PSum.rec (fun val => sizeOf val)
                              (fun val =>
                                PSum.rec (fun val => sizeOf val)
                                  (fun val => PSum.rec (fun val => sizeOf val) (fun val => sizeOf val) val) val)
                              (PSum.inr (PSum.inr (PSum.inr as)))))
                  a)
              a)
          a)
      a
-/
