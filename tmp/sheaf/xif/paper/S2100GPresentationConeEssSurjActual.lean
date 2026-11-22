import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual

/-!
# S2100: the literal S2094 presentation input is false

## Result

S2094 states the second full-2-universal input as

  `S2094GPresentationConeEssSurj`
    = forall (A B C : S1728Cover) (f : A -> C) (g : B -> C)
        (T) (ptA : T -> A.source.fiber)
        (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
        S1852ConeEssSurj Pg.

The field `EtaleStackBaseChangePresentation.isPullback` only records a weak
`EtalePseudofunctorSquare.TwoPullbackWitness`, and the statement above
quantifies over *all* weak presentations, not only coherent ones.  It is
therefore **false**: S1850's uniform doubled presentation is a genuine weak
presentation of the identity cover map (S1850Doubled), and S1852 proves that it
fails `S1852ConeEssSurj` (S1852Doubled_not_coneEssSurj).  Taking for the cover
map the identity cover map of S1850's doubled cover and for the point the S2086
point at the S1733 identity point gives a direct counterexample.

Consequently no presentation descent/pasting API can prove
`S2094GPresentationConeEssSurj`: the statement is refuted already at the
identity cover map, before any pasting is attempted.

## What is proved

* `S2100NotGPresentationConeEssSurj : ¬ S2094GPresentationConeEssSurj`:
  the refutation, by the doubled-presentation counterexample.

* `S2100StrongGPresentationInput`: the exact corrected input.  The quantifier
  must be over the *strong* presentation of the chosen `g.map` (a
  `StrongEtaleStackBaseChangePresentation`), not over an arbitrary weak
  `Pg`.  This is the datum S2086 actually uses when `g.map` carries a
  finite-etale structure.

* `S2100ConeEssSurj_of_strongGPresentationInput`: the corrected input gives
  full cone essential surjectivity of the chosen presentation, by projection
  from its strong field.  No inhabitant of the strong input is asserted; it is
  the remaining coherence/strongness input.

## Axiom footprint

No sorry, no new axiom, no fabricated presentation.  Only `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2100GPresentationConeEssSurjActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

/-! ## 1. The counterexample data -/

/-- The cover used in the counterexample: S1850's doubled-presentation cover. -/
noncomputable abbrev S2100CounterCover : S1728Cover := S1850DoubledCover

/-- The identity cover map of the counterexample cover.  Its underlying map is
definitionally `𝟙 S1850X.fiber`. -/
noncomputable abbrev S2100CounterMap :
    S1728CoverMap S2100CounterCover S2100CounterCover :=
  S1641CoverMapId S2100CounterCover

/-- The point at which the presentation is tested: the S1733 identity point. -/
noncomputable abbrev S2100CounterPoint :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
      S2100CounterCover.source.fiber :=
  S1733BasePoint

/-- The induced point of S2086, i.e. the C-point `ptA ; f.map`. -/
noncomputable abbrev S2100CounterPointC :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
      S2100CounterCover.source.fiber :=
  S2086PointC S2100CounterMap S2100CounterPoint

/-- The uniform doubled presentation of S1850, at the S2086 point.  It is a
genuine `EtaleStackBaseChangePresentation` of the identity cover map. -/
noncomputable abbrev S2100CounterPg :
    EtaleStackBaseChangePresentation S2100CounterMap.map S1726AffineOver
      (S2086PointC S2100CounterMap S2100CounterPoint) :=
  S1850Doubled S1726AffineOver (S2086PointC S2100CounterMap S2100CounterPoint)

/-- **The literal S2094 input is false.**  The cover map is the identity cover
map of S1850's doubled-presentation cover, and the presentation is S1850's
uniform doubled presentation at the S2086 point.  S1852 proves that this
presentation is not cone-essentially-surjective. -/
theorem S2100NotGPresentationConeEssSurj : ¬ S2094GPresentationConeEssSurj := by
  intro h
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  have hcone : S1852ConeEssSurj (S1850Doubled S1726AffineOver
      (S2086PointC S2100CounterMap S2100CounterPoint)) :=
    h S2100CounterCover S2100CounterCover S2100CounterCover
      S2100CounterMap S2100CounterMap S1726AffineOver S2100CounterPoint
      S2100CounterPg
  exact S1852Doubled_not_coneEssSurj S1726AffineOver
    (S2086PointC S2100CounterMap S2100CounterPoint) hne hcone

/-! ## 2. The exact corrected input -/

/-- The exact repair of S2094's second input: instead of quantifying over every
weak presentation `Pg`, require the strong presentation of the chosen cover map
`g.map` at the used point.  This is data, not a proposition derived from the
weak witness, and no inhabitant is asserted here. -/
def S2100StrongGPresentationInput : Type _ :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)

/-- The corrected input supplies the full cone essential surjectivity of the
chosen presentation, by projection from its strong field.  Unlike
`S2094GPresentationConeEssSurj`, this does not claim anything about an
arbitrary weak `Pg`. -/
theorem S2100ConeEssSurj_of_strongGPresentationInput
    (h : S2100StrongGPresentationInput)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S1852ConeEssSurj (h A B C f g T ptA).toWeak :=
  (h A B C f g T ptA).coneEssSurj

/-- The strong finite-etale field of a cover map selects a strong presentation,
so the corrected input is available from a strong geometric structure.  This
shows exactly what S2086 must assume instead of the false universal statement. -/
theorem S2100ConeEssSurj_of_strongFiniteEtale
    (hg : ∀ (A B C : S1728Cover) (f : S1728CoverMap A C)
      (g : S1728CoverMap B C), StrongEtaleStackFiniteEtaleMorphism g.map)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    S1852ConeEssSurj
      (((hg A B C f g).baseChange T (S2086PointC f ptA)).toWeak) :=
  ((hg A B C f g).baseChange T (S2086PointC f ptA)).coneEssSurj

/-! ## 3. Checks and axiom audit -/

#check S2100NotGPresentationConeEssSurj
#check S2100StrongGPresentationInput
#check S2100ConeEssSurj_of_strongGPresentationInput
#check S2100ConeEssSurj_of_strongFiniteEtale

#print axioms S2100NotGPresentationConeEssSurj
#print axioms S2100ConeEssSurj_of_strongGPresentationInput
#print axioms S2100ConeEssSurj_of_strongFiniteEtale

end LeanFormal.IUT.XiFPaper.S2100GPresentationConeEssSurjActual

end
