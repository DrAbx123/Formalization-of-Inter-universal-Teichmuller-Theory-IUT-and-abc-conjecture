import tmp.sheaf.xif.paper.TwoLthRootKummerActual
import Mathlib.FieldTheory.IntermediateField.Adjoin

/-! # Root-containing extension tensor: actual root and exact missing block

The actual 2l-th root hodgeTwoLthRoot T b lives in the algebraic closure of the
completion, not in the completion itself.  This file constructs the actual
intermediate field

  qVFamRootExtension T b = IntermediateField.adjoin K {root}

and proves the actual root lies in it.

ArithmeticTensorTupleBlock is built from FinitePlaceAtPrime data of a number
field K with a fixed rational prime p.  The root extension is an intermediate
field of the algebraic closure; the tree supplies neither a NumberField/
FinitePlaceAtPrime structure on it nor a normalized p-adic tensor/log-volume
block over it.  The exact target structure below records the missing finite
extension + normalized tensor block; no fake block is constructed.

No inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootExtensionTensorGapActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual root-containing intermediate field. -/
noncomputable def qVFamRootExtension :
    IntermediateField (Completion (qVPlace T b))
      (AlgebraicClosure (Completion (qVPlace T b))) :=
  IntermediateField.adjoin (Completion (qVPlace T b))
    {hodgeTwoLthRoot T b}

/-- The actual root lies in the constructed extension. -/
theorem qVFamRoot_mem_rootExtension :
    hodgeTwoLthRoot T b ∈ qVFamRootExtension T b :=
  IntermediateField.subset_adjoin _ (by simp)

/-- The actual root extension contains the completion field. -/
theorem qVFamRoot_completion_subset :
    (⊥ : IntermediateField (Completion (qVPlace T b))
      (AlgebraicClosure (Completion (qVPlace T b)))) ≤ qVFamRootExtension T b :=
  IntermediateField.bot_le _

/-- Exact missing finite normalized tensor block over a root-containing
extension: a finite-dimensional intermediate extension with a normalized p-adic
tensor carrier and log-volume, matching the root. -/
structure RootContainingTensorBlockTarget where
  extension : IntermediateField (Completion (qVPlace T b))
    (AlgebraicClosure (Completion (qVPlace T b)))
  root_mem : hodgeTwoLthRoot T b ∈ extension
  finiteDimensional : Module.Finite (Completion (qVPlace T b)) extension
  normedField : NormedField extension
  tensorIndex : Type
  tensorFintype : Fintype tensorIndex
  tensorBlock : Type
  tensorUnit : tensorBlock
  tensorLogVolume : tensorBlock → Real
  rootTensorValue : tensorBlock
  rootTensorValue_eq_log : tensorLogVolume rootTensorValue = 0

/-- The exact missing normalized root tensor block. -/
def RootThetaHullNormalizationGapActual : Prop :=
  Nonempty (RootContainingTensorBlockTarget T b)

end LeanFormal.IUT.XiFPaper.RootExtensionTensorGapActual

end
