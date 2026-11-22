
section Family3

variable {B C : S1728Cover}

/-- The second projection equation of the lift's action on cone morphisms. -/
theorem S2240LiftTwoCell_toY (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2240LiftTwoCell h f g T ptA m)
        (S2130Proj f g T ptA) =
      (S2240LiftToY h f g T ptA s).hom ≫ m.toY ≫
        (S2240LiftToY h f g T ptA t).inv := by
  exact @Subsingleton.elim _
    (S2185SubsingletonRepresentable (S := T)
      (f := Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W s)
        (S2130Proj f g T ptA))
      (g := Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W t)
        (S2130Proj f g T ptA))) _ _

/-- The first projection equation of the lift's action on cone morphisms. -/
theorem S2240LiftTwoCell_toX (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2240LiftTwoCell h f g T ptA m)
        (S2130ToSource f g T ptA) =
      (S2240LiftToX h f g T ptA s).hom ≫ m.toX ≫
        (S2240LiftToX h f g T ptA t).inv := by
  exact @Subsingleton.elim _
    (S2185Modification_subsingleton (C := B) (S2028CoverFiberDiscrete B)
      (F := Pseudofunctor.StrongTrans.vcomp
        (S2240Lift h f g T ptA W s) (S2130ToSource f g T ptA))
      (G := Pseudofunctor.StrongTrans.vcomp
        (S2240Lift h f g T ptA W t) (S2130ToSource f g T ptA))) _ _

/-- Two 2-cells into the strict apex with equal projections are equal. -/
theorem S2240TwoCell_ext (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {first second : Pseudofunctor.StrongTrans W (S2240Y (S2130P f g T ptA))}
    (alpha beta : first ⟶ second)
    (h1 : Pseudofunctor.StrongTrans.whiskerRight alpha (S2130ToSource f g T ptA) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S2130ToSource f g T ptA))
    (h2 : Pseudofunctor.StrongTrans.whiskerRight alpha (S2130Proj f g T ptA) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S2130Proj f g T ptA)) :
    alpha = beta := by
  exact @Subsingleton.elim _
    (S2185SubsingletonRepresentable (S := S2130P f g T ptA)
      (f := first) (g := second)) alpha beta

/-- The concrete two-pullback witness of the base square, at a fixed target cover and
under its presentation coherence. -/
noncomputable def S2240TwoPullbackWitness (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness where
  lift W c := S2240Lift h f g T ptA W c
  liftToX W c := S2240LiftToX h f g T ptA c
  liftToY W c := S2240LiftToY h f g T ptA c
  liftTwoCell W s t m := S2240LiftTwoCell h f g T ptA m
  liftTwoCell_toX W s t m := S2240LiftTwoCell_toX h f g T ptA m
  liftTwoCell_toY W s t m := S2240LiftTwoCell_toY h f g T ptA m
  twoCell_ext W first second alpha beta h1 h2 :=
    S2240TwoCell_ext h f g T ptA alpha beta h1 h2

end Family3
