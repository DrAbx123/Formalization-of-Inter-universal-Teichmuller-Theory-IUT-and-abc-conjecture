
/-- The S2130 base-change presentation at a strong target cover. -/
noncomputable def S2240HgFor_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) :=
  S2130PresentationOfWitness f g T ptA (S2240WitnessFor_strongCover Cs B A f g T ptA)

/-- Its projection is finite etale, unconditionally. -/
theorem S2240HgFor_strongCover_finiteEtale (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    IsFinite ((S2240HgFor_strongCover Cs B A f g T ptA).projection.left) ∧
      Etale ((S2240HgFor_strongCover Cs B A f g T ptA).projection.left) :=
  S2130PresentationOfWitness_finiteEtale f g T ptA
    (S2240WitnessFor_strongCover Cs B A f g T ptA)

#check S2240StrictConeIsoAt
#check S2240StrictConeIso_of_coneEssSurj
#check S2240ConcreteTwoPullback_of_coneEssSurj
#check S2240ConeEssSurj_doubled_false
#check S2240NotCPresentationConeEssSurj
#check S2240Hg_of_coneEssSurj
#check S2240ConeEssSurjAt
#check S2240ConeIsoAt
#check S2240ConeIsoAt_of_coneEssSurjAt
#check S2240WitnessFamily_of_coneEssSurjAt
#check S2240ConeEssSurjAt_of_strongCover
#check S2240WitnessFor_strongCover
#check S2240WitnessFor_coherent
#check S2240HgFor_strongCover
#check S2240HgFor_strongCover_finiteEtale

#print axioms S2240StrictConeIsoAt
#print axioms S2240StrictConeIso_of_coneEssSurj
#print axioms S2240ConcreteTwoPullback_of_coneEssSurj
#print axioms S2240ConeEssSurj_doubled_false
#print axioms S2240NotCPresentationConeEssSurj
#print axioms S2240Hg_of_coneEssSurj
#print axioms S2240ConeIsoAt_of_coneEssSurjAt
#print axioms S2240WitnessFamily_of_coneEssSurjAt
#print axioms S2240ConeEssSurjAt_of_strongCover
#print axioms S2240WitnessFor_strongCover
#print axioms S2240WitnessFor_coherent
#print axioms S2240HgFor_strongCover
#print axioms S2240HgFor_strongCover_finiteEtale

end LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual
