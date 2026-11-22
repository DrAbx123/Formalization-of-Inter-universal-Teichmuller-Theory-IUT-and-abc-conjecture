import tmp.sheaf.xif.paper.NativeGeneralTateSplitObstructionActual
import LeanFormal.IUT.Foundations.Geometry.LocalReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Minimal actual split-reduction certificate at a native bad lift

The source predicate unfolds to an existential variable change plus the
Mathlib split-multiplicative-reduction class over the adic completion integers.
This file records the explicit node/residue certificate, including the actual
split polynomial over the residue field, and proves it equivalent to the
source predicate. No general-q construction is asserted.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateSplitLocalCertificateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open Polynomial

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

noncomputable abbrev localPrime :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers T.arithmetic.F) :=
  NumberFieldFinitePlace.underlyingPrime ((nativeBadLift T).lift b)

noncomputable abbrev localField : Type :=
  (localPrime (l := l) T b).adicCompletion T.arithmetic.F

noncomputable abbrev localRing : Type :=
  (localPrime (l := l) T b).adicCompletionIntegers T.arithmetic.F

noncomputable abbrev localCurve : WeierstrassCurve (localField (l := l) T b) :=
  T.arithmetic.curve.curve.baseChange (localField (l := l) T b)

/-- Explicit minimal split-reduction certificate. -/
structure TateSplitLocalCertificate where
  coordinateChange : WeierstrassCurve.VariableChange (localField (l := l) T b)
  minimal :
    WeierstrassCurve.IsMinimal (localRing (l := l) T b)
      (coordinateChange • localCurve (l := l) T b)
  badReduction :
    (IsDiscreteValuationRing.maximalIdeal (localRing (l := l) T b)).valuation
      (localField (l := l) T b)
      (coordinateChange • localCurve (l := l) T b).Δ < 1
  c4_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal (localRing (l := l) T b)).valuation
      (localField (l := l) T b)
      (coordinateChange • localCurve (l := l) T b).c₄ = 1
  splitPolynomialSplits :
    letI : WeierstrassCurve.IsMinimal (localRing (l := l) T b)
        (coordinateChange • localCurve (l := l) T b) := minimal
    let W := coordinateChange • localCurve (l := l) T b
    let I := WeierstrassCurve.integralModel (localRing (l := l) T b) W
    Polynomial.Splits <|
      Polynomial.map
        (algebraMap (localRing (l := l) T b)
          (IsLocalRing.ResidueField (localRing (l := l) T b))) <|
        Polynomial.C I.c₄ * Polynomial.X ^ 2 +
          Polynomial.C (I.a₁ * I.c₄) * Polynomial.X -
          Polynomial.C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)

theorem TateSplitLocalCertificate.hasSplitMultiplicativeReduction
    (C : TateSplitLocalCertificate (l := l) T b) :
    (C.coordinateChange • localCurve (l := l) T b).HasSplitMultiplicativeReduction
      (localRing (l := l) T b) := by
  letI : WeierstrassCurve.IsMinimal (localRing (l := l) T b)
      (C.coordinateChange • localCurve (l := l) T b) := C.minimal
  exact
    { badReduction := C.badReduction
      multiplicativeReduction := C.c4_valuation_eq_one
      splitMultiplicativeReduction := C.splitPolynomialSplits }

theorem TateSplitLocalCertificate.toSourceSplit
    (C : TateSplitLocalCertificate (l := l) T b) :
    T.arithmetic.curve.HasSplitMultiplicativeReductionAt
      ((nativeBadLift T).lift b) := by
  dsimp [PuncturedEllipticCurve.HasSplitMultiplicativeReductionAt]
  exact ⟨C.coordinateChange, C.hasSplitMultiplicativeReduction⟩

noncomputable def TateSplitLocalCertificate.ofSourceSplit
    (h : T.arithmetic.curve.HasSplitMultiplicativeReductionAt
      ((nativeBadLift T).lift b)) :
    Nonempty (TateSplitLocalCertificate (l := l) T b) := by
  dsimp [PuncturedEllipticCurve.HasSplitMultiplicativeReductionAt] at h
  rcases h with ⟨C, hC⟩
  letI : WeierstrassCurve.IsMinimal (localRing (l := l) T b)
      (C • localCurve (l := l) T b) := hC.toIsMinimal
  exact ⟨
    { coordinateChange := C
      minimal := hC.toIsMinimal
      badReduction := hC.badReduction
      c4_valuation_eq_one := hC.multiplicativeReduction
      splitPolynomialSplits := hC.splitMultiplicativeReduction }⟩

theorem TateSplitLocalCertificate.nonempty_iff_sourceSplit :
    Nonempty (TateSplitLocalCertificate (l := l) T b) ↔
      T.arithmetic.curve.HasSplitMultiplicativeReductionAt
        ((nativeBadLift T).lift b) := by
  constructor
  · rintro ⟨C⟩
    exact C.toSourceSplit
  · intro h
    exact TateSplitLocalCertificate.ofSourceSplit (l := l) T b h

end LeanFormal.IUT.XiFPaper.NativeTateSplitLocalCertificateActual

end
