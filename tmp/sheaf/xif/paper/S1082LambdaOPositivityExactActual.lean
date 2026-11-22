import tmp.sheaf.xif.paper.S1081LambdaODomainHaarActual
import tmp.sheaf.xif.paper.UnitSmulCanonicalUnitReferenceActual

/-! # S1082: lambda-O positivity from full-rank scaled-unit containment

paperLambdaORegion(cRoot) = F(cRoot) O_hol is a full-rank Z_p-lattice.  The
exact full-rank witness used here is a unit u with
  u • O_canonical ⊆ F(cRoot) O_hol.
Then positivity is actual by the unit-smul canonical-reference Haar theorem
(the reference O has positive finite Haar and measure is monotone).
Finiteness is actual from S1081.  This avoids any fake coefficient identity or
closed-submodule positivity. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1082LambdaOPositivityExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1081LambdaODomainHaarActual
open LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact full-rank witness: a scaled canonical unit reference contained in the
paper lambda-O region. -/
def S1082ContainsScaledUnit : Prop :=
  ∃ u : (qVFamTensorBlock T b)ˣ,
    ((u : qVFamTensorBlock T b) •
      arithmeticTupleCanonicalUnitReference
        (qVFamTensorPlaces T b) qVFamTensorTuple) ⊆
      paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b)

/-- Full-rank scaled-unit containment gives actual positive domain Haar. -/
theorem s1082DomainPositivity_of_scaledUnit
    (h : S1082ContainsScaledUnit (l := l) T b) :
    S1080DomainPositivity (l := l) T b := by
  rcases h with ⟨u, hu⟩
  unfold S1080DomainPositivity
  exact lt_of_lt_of_le
    (measure_unit_smul_canonicalUnitReference_pos_lt_top
      (p := qVFamTensorP T b)
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (Measure.addHaar) u).1
    (measure_mono hu)

/-- Domain finiteness is actual (S1081). -/
theorem s1082DomainFiniteness_actual :
    S1080DomainFiniteness (l := l) T b :=
  s1081DomainFiniteness_actual (l := l) T b

/-- Exact minimum: the full-rank scaled-unit witness plus the pushforward
identity.  Positivity from the witness and finiteness are then actual. -/
def S1082ExactMinimum : Prop :=
  S1082ContainsScaledUnit (l := l) T b ∧
    S1080PushforwardHullEq (l := l) T b

end LeanFormal.IUT.XiFPaper.S1082LambdaOPositivityExactActual

end
