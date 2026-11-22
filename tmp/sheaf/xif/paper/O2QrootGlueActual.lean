/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual

/-!
# O2QrootGlueActual — qroot / 2ℓ-th root object glued from existing root assets

A511 object file: reuses the actual root-extension construction and the actual
root system from `S1929LiteralIQCarrierActual` / `PaperThetaRootObstructionActual`
(no new root construction).  The qroot is the root-system `2ℓ`-layer, packaged
as the unit `rootNormedUnit` and its field element; the power relation
`qroot^(2ℓ) = q` is the existing `rootNormedElement_L_pow`.

No comparison, no interface, no sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.O2QrootGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual qroot unit in the root extension `L_b`. -/
noncomputable def qrootUnit (b : Bad (nativePlaceSelection T)) :
    (rootNormedExtension T b)ˣ := rootNormedUnit T b

/-- The qroot as an element of `L_b`. -/
noncomputable def qrootElem (b : Bad (nativePlaceSelection T)) :
    rootNormedExtension T b := (qrootUnit T b : rootNormedExtension T b)

/-- The qroot is the actual root-system `2ℓ`-layer `sourceRoot`. -/
theorem qrootElem_eq_rootSystem (b : Bad (nativePlaceSelection T)) :
    qrootElem T b =
      (⟨(sourceRoot T b : rootNormedAmbient T b), rootNormedElement_mem T b⟩ :
        rootNormedExtension T b) := rfl

/-- The qroot is nonzero. -/
theorem qrootElem_ne_zero (b : Bad (nativePlaceSelection T)) :
    qrootElem T b ≠ 0 := (qrootUnit T b).ne_zero

/-- The `2ℓ`-th root relation `qroot^(2ℓ) = q` (reusing `rootNormedElement_L_pow`). -/
theorem qrootElem_pow (b : Bad (nativePlaceSelection T)) :
    (qrootElem T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) := by
  unfold qrootElem qrootUnit
  simpa [rootNormedUnit, sourceRootQUnit] using rootNormedElement_L_pow (T := T) b

/-- `_constructed`: the qroot object is the actual root-system layer, non-zero,
and satisfies the defining `2ℓ`-th power. -/
theorem qrootGlue_constructed (b : Bad (nativePlaceSelection T)) :
    qrootElem T b =
        (⟨(sourceRoot T b : rootNormedAmbient T b), rootNormedElement_mem T b⟩ :
          rootNormedExtension T b) ∧
      qrootElem T b ≠ 0 ∧
      (qrootElem T b) ^ (2 * l.value) =
        algebraMap (rootBase T b) (rootNormedExtension T b)
          ((qVFamily T b).q : rootBase T b) :=
  ⟨qrootElem_eq_rootSystem T b, qrootElem_ne_zero T b, qrootElem_pow T b⟩

#check qrootElem_pow
#check qrootGlue_constructed

end LeanFormal.IUT.XiFPaper.O2QrootGlueActual
end
