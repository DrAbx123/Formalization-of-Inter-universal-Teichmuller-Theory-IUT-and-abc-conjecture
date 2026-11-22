import tmp.sheaf.xif.paper.S2045OperationKummerActual
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

-- S2047: component (a) prerequisite: comap of the rational one-column place.
-- The completion model AlgEquiv/absolute Galois equivalence remains exact
-- missing because the two Algebra instances on adicCompletion are not defeq.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2047GaloisCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S2045OperationKummerActual

variable (v : FinitePrimePlace 2 7)

local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-- The rational one-column place is fixed by rational comap. -/
theorem S2047ComapQPlace :
    NumberFieldFinitePlace.comap (k := ℚ) (QPlace v) = QPlace v := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  simp only [QPlace, finitePrimePlaceToQ, LeanFormal.IUT.rationalFinitePlace,
    NumberField.FinitePlace.maximalIdeal_mk]
  change Ideal.comap (RingHom.id _)
    (LeanFormal.IUT.rationalHeightOneSpectrum v.1).asIdeal =
    (LeanFormal.IUT.rationalHeightOneSpectrum v.1).asIdeal
  rw [Ideal.comap_id]

/-- Exact first missing for (a): a ring/Alg equivalence between the two
completion models. -/
abbrev S2047BaseModelEquivRequired : Type :=
  Iut.SourceFinitePlaceReconstruction.Base (QPlace v) ≃+* ℚ_[v.1]

/-- Exact absolute Galois equivalence required in S2046. -/
abbrev S2047GaloisEquivRequired : Type := S2045GaloisEquiv (v := v)

/-- Exact target model comparison: the rational completion equivalence is
available at the Completion(comap) model; its identification with Base
(QPlace v) is the first missing conversion. -/
abbrev S2047RationalCompletionModelEquiv : Type :=
  LeanFormal.IUT.NumberFieldFinitePlace.Completion
      (NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)) ≃A[ℚ]
    LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField (QPlace v)

/-- Conditional reduction of the Galois equivalence in terms of a base ring
equivalence; the closure transport is the next missing construction. -/
structure S2047GaloisEquivOfBaseData where
  baseEquiv : S2047BaseModelEquivRequired (v := v)
  closureEquiv :
    AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) ≃+*
      AlgebraicClosure ℚ_[v.1]
  closure_compat :
    ∀ x : Iut.SourceFinitePlaceReconstruction.Base (QPlace v),
      closureEquiv (algebraMap _ _ x) = algebraMap _ _ (baseEquiv x)

abbrev S2047GaloisEquivOfBaseRequired : Type :=
  S2047GaloisEquivOfBaseData (v := v)

/-- The underlying height-one prime of QPlace v is the rational height-one prime at v.1. -/
theorem S2047UnderlyingPrimeQPlace :
    LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime (QPlace v) =
      LeanFormal.IUT.rationalHeightOneSpectrum v.1 := by
  simpa [QPlace, finitePrimePlaceToQ] using
    (LeanFormal.IUT.rationalFinitePlace_underlyingPrime (v.1))

#check S2047ComapQPlace
#check S2047UnderlyingPrimeQPlace
#check S2047BaseModelEquivRequired
#check S2047GaloisEquivRequired
#check S2047RationalCompletionModelEquiv
#check S2047GaloisEquivOfBaseData
#check S2047GaloisEquivOfBaseRequired

#print axioms S2047ComapQPlace
#print axioms S2047UnderlyingPrimeQPlace

end LeanFormal.IUT.XiFPaper.S2047GaloisCompletionActual

end