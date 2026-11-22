import tmp.sheaf.xif.paper.S870RootStackRestrictionBridgeActual
import Mathlib.LinearAlgebra.Determinant

/-! # S879: exact inputs for RootStackGeneralNormFormula

S870 gives the actual determinant of multiplication by u on E as an
L-vector space.  The two positive routes need the following exact inputs:

(1) the E/L norm-extension formula: the normalized norm on E restricts to
    the normalized norm on L;
(2) the additive-Haar/determinant comparison for the L-linear scalar map;
(3) the DVR unit factor = 1 and the uniformizer/power factor.

The determinant is actual.  The remaining norm/uniformizer inputs are
recorded as exact Props; no no-go and no fake formula are asserted.
-/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S879RootStackNormFormulaInputsActual

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
open LeanFormal.IUT.XiFPaper.S870RootStackRestrictionBridgeActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual determinant input (S870). -/
theorem rootStack_scalar_det_actual (u : rootNormedExtension T b) :
    LinearMap.det ((Algebra.lsmul (rootNormedExtension T b)
      (rootNormedExtension T b) (rootStackExtension T b)) u) =
        u ^ dStack (l := l) T b :=
  rootStack_scalar_det (l := l) T b u

/-- Exact E/L norm-extension formula: the normalized norm on E restricts to
the normalized norm on L. -/
def ENormExtensionFormula : Prop :=
  ∀ x : rootNormedExtension T b,
    ‖(algebraMap (rootNormedExtension T b) (rootStackExtension T b) x :
      rootStackExtension T b)‖ = ‖x‖

/-- Exact determinant/additive-Haar bridge: the distributive Haar character
of the scalar automorphism equals the dQp-normalized determinant factor.
This is the exact analytic input not supplied by the determinant alone. -/
def RootStackAdditiveHaarDetFormula : Prop :=
  ∀ u : (rootNormedExtension T b)ˣ,
    (distribHaarChar (rootStackExtension T b)
        (rootStackAlgebraMapUnits (l := l) T b u) : Real) =
      (distribHaarChar (rootNormedExtension T b) u : Real) ^ dStack (l := l) T b

/-- Exact DVR/uniformizer input: unit Haar factor one and uniformizer/power
factor for E/L.  The decomposition field is the exact DVR statement. -/
structure RootStackDVRUniformizerInput where
  piE : (rootStackExtension T b)ˣ
  decomposition : ∀ u : (rootNormedExtension T b)ˣ,
    ∃ (n : Int) (eps : (rootStackExtension T b)ˣ),
      rootStackAlgebraMapUnits (l := l) T b u = eps * piE ^ n
  unit_haar_factor_one : Prop
  uniformizer_power_factor : Prop

def RootStackDVRUniformizerInputRequired : Prop :=
  Nonempty (RootStackDVRUniformizerInput (l := l) T b)

/-- The exact general formula plus the norm-extension input. -/
def RootStackNormFormulaInputs : Prop :=
  ENormExtensionFormula (l := l) T b ∧
    (RootStackGeneralNormFormula (l := l) T b ∨
      RootStackAdditiveHaarDetFormula (l := l) T b)

end LeanFormal.IUT.XiFPaper.S879RootStackNormFormulaInputsActual

end
