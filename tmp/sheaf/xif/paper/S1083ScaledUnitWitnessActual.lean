import tmp.sheaf.xif.paper.S1082LambdaOPositivityExactActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # S1083: construct the scaled-unit witness for lambda-O positivity

Choose an integer N with cRoot <= N (cRoot = order/(2l) is finite and
nonnegative).  A pure fractional scaling datum at the constant coefficient N
gives a unit
  u = arithmeticTupleFractionalGeneratorUnit ... data
with u • O_canonical = F(N) O_hol.  Since cRoot <= N, the fractional lattice
F(N) is contained in F(cRoot), hence u • O ⊆ F(cRoot) O_hol =
paperLambdaORegion(cRoot).  This yields S1082ContainsScaledUnit and then actual
domain positivity by S1082.

The integer scaling datum and the bound cRoot <= N are exact inputs (the
construction of the datum at integer N is not faked). -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1083ScaledUnitWitnessActual

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
open LeanFormal.IUT.XiFPaper.S1082LambdaOPositivityExactActual
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

/-- Integer pure scaling datum at constant coefficient N, plus the bound
cRoot <= N. -/
structure S1083IntegerWitness where
  N : Nat
  data : ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => (N : Real))
  bound : ∀ i : qVFamTensorV,
    paperRootCoefficientFamily (l := l) T b i ≤ (N : Real)

/-- The constructed unit and containment u • O ⊆ paperLambdaORegion(cRoot). -/
theorem s1083ScaledUnitContainment_of_witness
    (W : S1083IntegerWitness (l := l) T b) :
    S1082ContainsScaledUnit (l := l) T b := by
  refine ⟨arithmeticTupleFractionalGeneratorUnit
    (qVFamTensorPlaces T b) qVFamTensorTuple W.data, ?_⟩
  intro x hx
  have hgen := arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    (qVFamTensorPlaces T b) qVFamTensorTuple W.data
  rw [arithmeticTupleFractionalGeneratorUnit_coe] at hx
  have hxN : x ∈ ((arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => (W.N : Real)) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b)) := by
    rw [hgen]
    exact hx
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun _ => (W.N : Real)) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    exact W.bound i
  exact (mul_le_mul' hlat le_rfl) hxN

/-- Actual domain positivity from the integer witness. -/
theorem s1083DomainPositivity_of_witness
    (W : S1083IntegerWitness (l := l) T b) :
    S1080DomainPositivity (l := l) T b :=
  s1082DomainPositivity_of_scaledUnit (l := l) T b
    (s1083ScaledUnitContainment_of_witness (l := l) T b W)

/-- Exact minimum: integer scaling witness + pushforward identity. -/
def S1083ExactMinimum : Prop :=
  Nonempty (S1083IntegerWitness (l := l) T b) ∧
    S1080PushforwardHullEq (l := l) T b

end LeanFormal.IUT.XiFPaper.S1083ScaledUnitWitnessActual

end
