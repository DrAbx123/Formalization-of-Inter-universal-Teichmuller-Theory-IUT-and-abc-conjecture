
section Family4

variable {B C : S1728Cover}

/-- The full family of concrete two-pullback witnesses for a fixed target cover, from its
presentation coherence. -/
noncomputable def S2240WitnessFamily (h : S2240ConeIsoAt B C) :
    forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
      (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  fun A f g T ptA => S2240TwoPullbackWitness h f g T ptA

/-- The same family, from the cone essential surjectivity of the C-presentation. -/
noncomputable def S2240WitnessFamily_of_coneEssSurjAt (h : S2240ConeEssSurjAt B C) :
    forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
      (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  S2240WitnessFamily (S2240ConeIsoAt_of_coneEssSurjAt B C h)

end Family4

/-- **A strong target cover satisfies the presentation coherence.**  The finite-etale
structure underlying a StrongCover carries the full 2-universal property at every point,
and its recorded weak presentation is definitionally the same presentation used by S2130. -/
theorem S2240ConeEssSurjAt_of_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) :
    S2240ConeEssSurjAt B (StrongCover.cover Cs) := by
  intro A f g T ptA
  exact (Cs.finiteEtale.baseChange T (S2130PtX f T ptA)).coneEssSurj

/-- **The concrete two-pullback witness for a strong target cover.** -/
noncomputable def S2240WitnessFor_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  S2240WitnessFamily_of_coneEssSurjAt (S2240ConeEssSurjAt_of_strongCover Cs B)
    A f g T ptA

/-- **The concrete two-pullback witness for a coherent target cover.** -/
noncomputable def S2240WitnessFor_coherent (Cs : CoherentCover)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (CoherentCover.cover Cs))
    (g : S1728CoverMap B (CoherentCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  S2240WitnessFor_strongCover Cs.toStrongCover B A f g T ptA