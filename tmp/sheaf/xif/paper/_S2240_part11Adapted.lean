
/-- **The coherence hypothesis fails at the doubled cover of S1850.**  The presentation of
the identity structure map at the identity point is S1850Doubled, and S1852 proves that it
is not cone-essentially-surjective. -/
theorem S2240ConeEssSurj_doubled_false :
    ¬ S1852ConeEssSurj
      (S2130PC (A := S1850DoubledCover) (C := S1850DoubledCover)
        (f := S1641CoverMapId S1850DoubledCover) S1726AffineOver S1733BasePoint) := by
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  exact S1852Doubled_not_coneEssSurj S1726AffineOver
    (S2130PtX (S1641CoverMapId S1850DoubledCover) S1726AffineOver S1733BasePoint) hne

/-- **The uniform coherence hypothesis is false.**  Consequently it cannot be used to
close the uniform S2130 target: the strong-presentation property is refuted by the doubled
cover, exactly as S2100 refutes the uniform strong presentation input. -/
theorem S2240NotCPresentationConeEssSurj : ¬ S2240CPresentationConeEssSurj := by
  intro h
  exact S2240ConeEssSurj_doubled_false
    (h S1850DoubledCover S1850DoubledCover S1850DoubledCover
      (S1641CoverMapId S1850DoubledCover) (S1641CoverMapId S1850DoubledCover)
      S1726AffineOver S1733BasePoint)

/-- The same statement in the recorded first-missing form. -/
theorem S2240NotFirstMissing : ¬ S2240FirstMissing := S2240NotCPresentationConeEssSurj

/-- The S2130 finite-etale presentations of the C-cover, from the coherence. -/
noncomputable def S2240Hg_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
      EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) :=
  S2130ConcreteHgOfTwoPullback (S2240ConcreteTwoPullback_of_coneEssSurj h)

