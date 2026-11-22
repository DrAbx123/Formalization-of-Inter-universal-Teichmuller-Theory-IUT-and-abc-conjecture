import tmp.sheaf.xif.paper.S921RQpilotPaperRegionPositivityActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor

/-! # S923: interior nonempty for R = F(cRoot) * O_hol

R contains the fractional lattice F = arithmeticTupleFractionalLattice cRoot,
because 1 ∈ O_hol.  F contains 0.  Hence if F is open, F ⊆ interior R and
interior R is nonempty.  The exact minimal input is openness of F; the
standard tensor-span criterion reduces it to `isOpen_submoduleTensorSpan` and
the local span-top condition.  No equality/scaling data is used.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The paper fractional lattice F(cRoot). -/
noncomputable def s923F : Set (qVFamTensorBlock T b) :=
  (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b) :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b))

theorem s923F_zero_mem : (0 : qVFamTensorBlock T b) ∈ s923F (l := l) T b :=
  Submodule.zero_mem _

/-- F(cRoot) is contained in R = F(cRoot) * O_hol. -/
theorem s923F_subset_R : s923F (l := l) T b ⊆ s914R (l := l) T b := by
  intro x hx
  unfold s923F at hx
  change x ∈ qPilotPaperRegion (l := l) T b
  unfold qPilotPaperRegion thetaTensorScaledRegion
  have h1 : (1 : qVFamTensorBlock T b) ∈
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple := by
    change IsIntegral ℤ_[(qVFamTensorP T b)] (1 : qVFamTensorBlock T b)
    exact isIntegral_one
  have hmul := Submodule.mul_mem_mul hx h1
  simpa using hmul

/-- Exact minimal openness input: the fractional lattice F(cRoot) is open. -/
def S923FractionalLatticeOpen : Prop :=
  IsOpen (s923F (l := l) T b)

/-- Openness of F gives nonempty interior of R. -/
theorem s923R_interior_nonempty_of_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    S921RInteriorNonempty (l := l) T b := by
  refine ⟨0, ?_⟩
  exact interior_maximal (s923F_subset_R (l := l) T b) hopen
    (s923F_zero_mem (l := l) T b)

/-- Conditional actual positivity of R from openness of F. -/
theorem s923R_measure_pos_of_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    0 < MeasureTheory.Measure.addHaar (s914R (l := l) T b) := by
  exact s921R_measure_pos_of_interior (l := l) T b MeasureTheory.Measure.addHaar
    (s923R_interior_nonempty_of_open (l := l) T b hopen)

/-- Exact positivity goal (same as S921). -/
def S923RMeasurePositive : Prop :=
  0 < MeasureTheory.Measure.addHaar (s914R (l := l) T b)

end LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual

end
