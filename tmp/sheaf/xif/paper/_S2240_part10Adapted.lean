
/-- The exact coherence hypothesis: every C-presentation carries the full 2-universal
property (cone essential surjectivity). -/
def S2240CPresentationConeEssSurj : Prop :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
    S1852ConeEssSurj (S2130PC f T ptA)

/-- **S2185StrictConeIso from the presentation coherence.** -/
theorem S2240StrictConeIso_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    S2185StrictConeIso :=
  fun A B C f g T ptA W c => S2240StrictConeIsoAt f g T ptA (h A B C f g T ptA) c

/-- **The S2130 concrete two-pullback from the presentation coherence.** -/
noncomputable def S2240ConcreteTwoPullback_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    S2130ConcreteTwoPullback :=
  S2185ConcreteTwoPullback_of_strictConeIso (S2240StrictConeIso_of_coneEssSurj h)

/-- The exact first missing statement: the C-presentation coherence. -/
def S2240FirstMissing : Prop := S2240CPresentationConeEssSurj

/-- Conditional form: the S2130 target from the recorded exact first missing. -/
noncomputable def S2240ConcreteTwoPullback_of_firstMissing (h : S2240FirstMissing) :
    S2130ConcreteTwoPullback :=
  S2240ConcreteTwoPullback_of_coneEssSurj h