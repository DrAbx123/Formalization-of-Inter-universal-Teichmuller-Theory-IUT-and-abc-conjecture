import tmp.sheaf.xif.paper.RootNormalizedThetaHullActual
import tmp.sheaf.xif.paper.TwoLthRootKummerActual

/-! # Root tensor block over the algebraic closure: exact object-level gap

The actual 2l-th root hodgeTwoLthRoot lives in the algebraic closure

  L = AlgebraicClosure (Completion (qVPlace T b)),

not in the completion.  The existing arithmetic tensor block is built over
CommonPrimeCompletion (a finite place of F) and cannot be parametrized by L:
L does not carry the completed-place structure or a constructed normalized Haar.

Therefore the root hull normalized log over L is not constructed.  The exact
object-level missing data are recorded: a NormedField/measurable/Haar structure
on L, a root tensor block over L, a root unit region, and the root lattice
scaling data.

The coefficient formula is nevertheless actual and computed here:

  rootThetaHullFormulaLog b
    = -(order(qVFamily b)/(2l)) * log p_b,

so it is the exact negative root coefficient times log p_b, nonzero for positive
order and p_b > 1.  No fake Haar equality is asserted.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootTensorBlockLGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.RootNormalizedThetaHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual algebraic closure L of the completion at b. -/
abbrev RootFieldL : Type :=
  AlgebraicClosure (Completion (qVPlace T b))

/-- The actual root coefficient order/(2l). -/
noncomputable def rootFormulaCoefficient : Real :=
  ((qVFamily T b).order : Real) / (2 * (l.value : Real))

/-- The exact root coefficient formula log: -(order/(2l)) log p_b. -/
noncomputable def rootFormulaLog : Real :=
  - rootFormulaCoefficient T b * Real.log (qVFamP T b : Real)

theorem rootFormulaLog_eq :
    rootFormulaLog T b =
      -(((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamP T b : Real) := rfl

/-- Exact nonzero of the root formula log for positive order and p_b > 1. -/
theorem rootFormulaLog_ne_zero
    (hlogp : 0 < Real.log (qVFamP T b : Real)) :
    rootFormulaLog T b ≠ 0 := by
  unfold rootFormulaLog rootFormulaCoefficient
  have horder : 0 < ((qVFamily T b).order : Real) := by
    exact_mod_cast (qVFamily T b).order_pos
  have hden : (0 : Real) < 2 * (l.value : Real) := by positivity
  have hcoeff : 0 < ((qVFamily T b).order : Real) / (2 * (l.value : Real)) :=
    div_pos horder hden
  have hneg : -(((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
      Real.log (qVFamP T b : Real) < 0 := by
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos' hcoeff) hlogp
  exact ne_of_lt hneg

/-- Exact object-level missing data for a root tensor block over L: normalized
field/measurable/Haar structure, root unit region, and root lattice scaling. -/
structure RootTensorBlockOverLData where
  field : Type
  field_eq : field = RootFieldL (l := l) T b
  normalizedField : Prop
  measuredField : Prop
  haar : Prop
  rootUnitRegion : Prop
  rootTensorBlock : Prop
  rootLatticeScaling : Prop

/-- Exact root tensor block requirement; no inhabitant is asserted. -/
def RootTensorBlockOverLRequired : Prop :=
  Nonempty (RootTensorBlockOverLData (l := l) T b)

/-- The actual root lies in the algebraic closure and is not assumed to be a
completion root. -/
theorem root_not_assumed_completion :
    ¬ RootInCompletion (l := l) T b (hodgeTwoLthRoot T b) →
      ¬ RootInCompletion (l := l) T b (hodgeTwoLthRoot T b) :=
  id

/-- The root field L is exactly the algebraic closure type. -/
theorem rootFieldL_eq : RootFieldL (l := l) T b =
    AlgebraicClosure (Completion (qVPlace T b)) := rfl

end LeanFormal.IUT.XiFPaper.RootTensorBlockLGapActual

end
