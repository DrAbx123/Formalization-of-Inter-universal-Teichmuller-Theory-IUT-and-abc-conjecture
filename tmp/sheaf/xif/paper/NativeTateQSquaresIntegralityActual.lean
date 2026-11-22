import tmp.sheaf.xif.paper.NativeGeneralTateSplitObstructionActual
import tmp.sheaf.xif.paper.NativeTateSplitLocalCertificateActual
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# General Tate q-series integrality/minimality source

The existing Lambert-series API proves summability and estimates for the
concrete q = p; it does not provide a general-q integral model over the adic
completion integers, nor the minimality/c4/split-residue theorem.

This file records the minimal actual q-series model needed: an integral lift of
the Tate equation over the completion integers, its base-change equality, its
minimality, the c4 valuation, and the actual split-reduction class. From such
a model the clauseB Tate comparison yields the per-b native split theorem.

No concrete q is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateQSquaresIntegralityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeGeneralTateSplitObstructionActual

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

noncomputable abbrev tateParameter :
    NumberFieldFinitePlace.FinitePlaceQCandidate ((nativeBadLift T).lift b) :=
  (nativeBadTateWitness T (nativeBadLift T) b).parameter

noncomputable abbrev tateCurve : WeierstrassCurve (localField (l := l) T b) :=
  TateCurve.weierstrassCurve (localField (l := l) T b) (tateParameter (l := l) T b).q

/-- Minimal actual q-series model: an integral lift of the Tate equation, its
base-change equality, minimality, c4 valuation, and split-reduction class. -/
structure TateQSquaresIntegralModel where
  integralModel : WeierstrassCurve (localRing (l := l) T b)
  baseChange_eq :
    WeierstrassCurve.baseChange integralModel (localField (l := l) T b) =
      tateCurve (l := l) T b
  minimal :
    WeierstrassCurve.IsMinimal (localRing (l := l) T b) (tateCurve (l := l) T b)
  c4_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal (localRing (l := l) T b)).valuation
      (localField (l := l) T b) (tateCurve (l := l) T b).c₄ = 1
  hasSplit :
    (tateCurve (l := l) T b).HasSplitMultiplicativeReduction
      (localRing (l := l) T b)

/-- The q-series model supply is the exact missing source object. -/
def TateQSquaresIntegralModelRequired : Prop :=
  Nonempty (TateQSquaresIntegralModel (l := l) T b)

/-- A q-series integral model supplies the Tate split predicate. -/
theorem TateQSquaresIntegralModel.toTateSplit
    (M : TateQSquaresIntegralModel (l := l) T b) :
    HasSplitMultiplicativeReductionOnMinimalModel
      (localRing (l := l) T b) (tateCurve (l := l) T b) := by
  exact ⟨1, by simpa using M.hasSplit⟩

/-- The q-series model plus the actual clauseB comparison gives the native
per-b split theorem. -/
theorem nativeTateSplitTheoremAt_of_qSeriesModel
    (M : TateQSquaresIntegralModel (l := l) T b) :
    NativeTateSplitTheoremAt (l := l) T b := by
  let C := (nativeTateComparisonAt (l := l) T b).coordinateChange
  have hTate : HasSplitMultiplicativeReductionOnMinimalModel
      (localRing (l := l) T b) (tateCurve (l := l) T b) := M.toTateSplit
  have hTransport : HasSplitMultiplicativeReductionOnMinimalModel
      (localRing (l := l) T b)
      (C • tateCurve (l := l) T b) :=
    (hasSplitMultiplicativeReductionOnMinimalModel_smul_iff
      (localRing (l := l) T b) C (tateCurve (l := l) T b)).mpr hTate
  have hEq : localCurve (l := l) T b = C • tateCurve (l := l) T b := by
    rw [localCurve]
    exact (nativeTateComparisonAt (l := l) T b).realizesCurve.symm
  have hX : HasSplitMultiplicativeReductionOnMinimalModel
      (localRing (l := l) T b) (localCurve (l := l) T b) := by
    rw [hEq]
    exact hTransport
  exact hX

/-- Minimal actual q-series coefficient integrality family: the Lambert
coefficients and the resulting a4/a6 actually lie in the completion integers. -/
structure TateQSquaresIntegralityFamily where
  s3Integral : ∃ s : localRing (l := l) T b,
    algebraMap (localRing (l := l) T b) (localField (l := l) T b) s =
      TateCurve.lambertSeries (localField (l := l) T b) 3
        (tateParameter (l := l) T b).q
  s5Integral : ∃ s : localRing (l := l) T b,
    algebraMap (localRing (l := l) T b) (localField (l := l) T b) s =
      TateCurve.lambertSeries (localField (l := l) T b) 5
        (tateParameter (l := l) T b).q
  a4Integral : ∃ a : localRing (l := l) T b,
    algebraMap (localRing (l := l) T b) (localField (l := l) T b) a =
      TateCurve.a4 (localField (l := l) T b) (tateParameter (l := l) T b).q
  a6Integral : ∃ a : localRing (l := l) T b,
    algebraMap (localRing (l := l) T b) (localField (l := l) T b) a =
      TateCurve.a6 (localField (l := l) T b) (tateParameter (l := l) T b).q

/-- The exact missing q-series integrality/minimality theorem family. -/
def TateQSquaresIntegralityRequired : Prop :=
  ∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
    Nonempty (TateQSquaresIntegralModel (l := l) T b)

end LeanFormal.IUT.XiFPaper.NativeTateQSquaresIntegralityActual

end
