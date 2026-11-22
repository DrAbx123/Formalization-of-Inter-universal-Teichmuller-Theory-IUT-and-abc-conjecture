import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamRootThetaTensorLiftActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual

-- S1143: q_v-dependent Theta pilot and hull, built directly from the
-- actual qVFamily q_v.  No fixed q=1/5 and no theta-1 substitution.
-- Actual: value root, tensor coefficient, L-valued tensor lift, paper hull.
-- Exact: mu_{2l} tensor lift and paper hull formula gap.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1143QvDependentThetaPilotHullActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamRootThetaTensorLiftActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (j : SignedLabel l.value)

/-- Actual q_v-dependent Theta pilot at (b,j): root value, tensor
coefficient, and L-valued tensor lift, all from qVFamily q_v. -/
structure S1143ThetaPilotAt where
  rootValue : (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  rootValue_eq : rootValue = qVFamPaperThetaValueRoot T b j
  tensorCoefficient : Real
  tensorCoefficient_eq : tensorCoefficient =
    qVFamPaperThetaTensorCoefficient T b j
  tensorLift : rootTensorBlock T b
  tensorLift_eq : tensorLift = qVFamRootThetaTensorLift T b j

noncomputable def s1143ThetaPilotAt : S1143ThetaPilotAt (l := l) T b j where
  rootValue := qVFamPaperThetaValueRoot T b j
  rootValue_eq := rfl
  tensorCoefficient := qVFamPaperThetaTensorCoefficient T b j
  tensorCoefficient_eq := rfl
  tensorLift := qVFamRootThetaTensorLift T b j
  tensorLift_eq := rfl

/-- The actual value root is the 2l-th root power q_v^{j^2}. -/
theorem s1143RootValue_formula :
    (s1143ThetaPilotAt T b j).rootValue =
      (hodgeTwoLthRoot T b) ^ (gaussExponent j.1).toNat :=
  qVFamPaperThetaValueRoot_formula T b j

/-- The actual tensor coefficient is j^2 * order(q_v)/(2l). -/
theorem s1143TensorCoefficient_formula :
    (s1143ThetaPilotAt T b j).tensorCoefficient =
      ((gaussExponent j.1).toNat : Real) *
        (((qVFamily T b).order : Real) / (2 * (l.value : Real))) := by
  rw [(s1143ThetaPilotAt T b j).tensorCoefficient_eq]
  unfold qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
  rfl

/-- The L-valued tensor lift lies in the actual root Theta tensor image. -/
theorem s1143TensorLift_mem_image :
    (s1143ThetaPilotAt T b j).tensorLift ∈
      qVFamRootThetaTensorImageSet (l := l) T b := by
  rw [(s1143ThetaPilotAt T b j).tensorLift_eq]
  exact qVFamRootThetaTensorLift_mem_image T b j

/-- Actual q_v-dependent paper Theta hull: paperRootThetaHull at cRoot=order/(2l). -/
structure S1143ThetaHullAt where
  hull : Set (qVFamTensorBlock T b)
  hull_eq : hull = paperRootThetaHull (l := l) T b
  coefficient : Real
  coefficient_eq : coefficient = qVFamPaperRootCoefficient (l := l) T b

noncomputable def s1143ThetaHullAt : S1143ThetaHullAt (l := l) T b where
  hull := paperRootThetaHull (l := l) T b
  hull_eq := rfl
  coefficient := qVFamPaperRootCoefficient (l := l) T b
  coefficient_eq := rfl

theorem s1143ThetaHull_coefficient_formula :
    (s1143ThetaHullAt (l := l) T b).coefficient =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) :=
  rfl

/-- Exact Theta mu_{2l} tensor-lift gap (no root-of-unity action constructed). -/
def S1143ThetaMuTensorLiftRequired : Prop :=
  QVFamRootThetaMuTensorLiftGapRequired (l := l) T b

/-- Exact paper hull formula gap: requires scaling data and hull equality. -/
def S1143ThetaHullFormulaRequired : Prop :=
  Nonempty (PaperRootHullFormulaGap (l := l) T b)

#check s1143ThetaPilotAt
#check s1143RootValue_formula
#check s1143TensorCoefficient_formula
#check s1143TensorLift_mem_image
#check s1143ThetaHullAt
#check S1143ThetaMuTensorLiftRequired
#check S1143ThetaHullFormulaRequired

end LeanFormal.IUT.XiFPaper.S1143QvDependentThetaPilotHullActualAdapted

end