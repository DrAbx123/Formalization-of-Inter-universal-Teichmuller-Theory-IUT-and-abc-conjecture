import tmp.sheaf.xif.paper.S866RootStackCharacterNormLiftActual
import Mathlib.LinearAlgebra.Determinant

/-! # S870: restriction bridge via the L-vector-space determinant

`rootStackExtension` is an L-vector space of degree `dStack`.  Multiplication
by `algebraMap u` is the L-linear map `lsmul L E u`, whose determinant is
`u ^ dStack` (Mathlib `LinearMap.det_lsmul`).  This is actual.  The remaining
analytic input is the general Haar-character/norm formula

  dHC_E(algebraMap u) = dHC_L(u) ^ dStack,

from which the S866 restriction bridge follows by taking logs.  No fake
analytic formula is asserted.
-/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S870RootStackRestrictionBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S866RootStackCharacterNormLiftActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual determinant of multiplication by u on E as an L-vector space. -/
theorem rootStack_scalar_det (u : rootNormedExtension T b) :
    LinearMap.det ((Algebra.lsmul (rootNormedExtension T b)
      (rootNormedExtension T b) (rootStackExtension T b)) u) =
        u ^ dStack (l := l) T b := by
  letI : Module.Free (rootNormedExtension T b) (rootStackExtension T b) :=
    Module.Free.of_divisionRing _ _
  simpa [dStack] using
    (Algebra.det_lsmul (R := rootNormedExtension T b)
      (S := rootStackExtension T b) u)

/-- Exact general Haar-character/norm formula: dHC_E(algebraMap u) is the
dStack-th power of dHC_L(u). -/
def RootStackGeneralNormFormula : Prop :=
  ∀ u : (rootNormedExtension T b)ˣ,
    distribHaarChar (rootStackExtension T b)
        (rootStackAlgebraMapUnits (l := l) T b u) =
      (distribHaarChar (rootNormedExtension T b) u) ^ dStack (l := l) T b

def RootStackGeneralNormFormulaRequired : Prop :=
  RootStackGeneralNormFormula (l := l) T b

/-- The exact general formula implies S866's restriction bridge by logarithms. -/
theorem rootStackHaarCharRestrictionBridge_of_generalNormFormula
    (h : RootStackGeneralNormFormula (l := l) T b) :
    RootStackHaarCharRestrictionBridge (l := l) T b 0 := by
  intro u
  have h' := h u
  have hE : (distribHaarChar (rootStackExtension T b)
      (rootStackAlgebraMapUnits (l := l) T b u) : Real) =
      ((distribHaarChar (rootNormedExtension T b) u : NNReal) : Real) ^
        dStack (l := l) T b := by
    rw [h']
    simp [NNReal.coe_pow]
  rw [hE, Real.log_pow]

end LeanFormal.IUT.XiFPaper.S870RootStackRestrictionBridgeActual

end
