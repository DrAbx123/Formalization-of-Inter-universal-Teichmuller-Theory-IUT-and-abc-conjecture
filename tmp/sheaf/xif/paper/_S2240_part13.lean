
section Family2

variable {B C : S1728Cover}

/-- Morphism of the PB-cones induced by a morphism of the base cones. -/
noncomputable def S2240ConePBMorphism
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    (S2185PBSquare f g T ptA).ConeMorphism (S2185ConePB f g T ptA s)
      (S2185ConePB f g T ptA t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    exact @Subsingleton.elim _ (S2185SubsingletonOrbicurve
      (f := Pseudofunctor.StrongTrans.vcomp (S2185ConePB f g T ptA s).toX
        (S2185PBSquare f g T ptA).xToBase)
      (g := Pseudofunctor.StrongTrans.vcomp (S2185ConePB f g T ptA t).toY
        (S2185PBSquare f g T ptA).yToBase)) _ _

/-- Morphism of the strict cones induced by a morphism of the base cones. -/
noncomputable def S2240ConeStrictMorphism (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    (S2185StrictSquare f g T ptA).ConeMorphism (S2240StrictCone h f g T ptA s)
      (S2240StrictCone h f g T ptA t) where
  toX := (S2130PB f g T ptA).isPullback.liftTwoCell W
    (S2185ConePB f g T ptA s) (S2185ConePB f g T ptA t)
    (S2240ConePBMorphism f g T ptA m)
  toY := m.toY
  compatibility := by
    exact @Subsingleton.elim _ (S2185SubsingletonRepresentable
      (S := (S2130PC f T ptA).pullbackScheme)
      (f := Pseudofunctor.StrongTrans.vcomp (S2240StrictCone h f g T ptA s).toX
        (S2185StrictSquare f g T ptA).xToBase)
      (g := Pseudofunctor.StrongTrans.vcomp (S2240StrictCone h f g T ptA t).toY
        (S2185StrictSquare f g T ptA).yToBase)) _ _

/-- The action of the lift on cone morphisms. -/
noncomputable def S2240LiftTwoCell (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    S2240Lift h f g T ptA W s ⟶ S2240Lift h f g T ptA W t :=
  (S2240StrictWitness f g T ptA).liftTwoCell W
    (S2240StrictCone h f g T ptA s) (S2240StrictCone h f g T ptA t)
    (S2240ConeStrictMorphism h f g T ptA m)

end Family2
