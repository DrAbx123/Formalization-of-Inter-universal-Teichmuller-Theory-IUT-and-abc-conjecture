import tmp.sheaf.xif.paper.S1231SourceCoreActual

/-! # S1237: no positive sourceLevel on Choice = I.family.index

sourceInd1 and sourceInd3 both act by horizontal shifts at the base point:
  sourceInd1 (-1) (indexOf 0 0) = indexOf 1 0 = sourceInd3 1 (indexOf 0 0).
Thus any sourceLevel invariant under ind1 while ind3 adds n is contradictory
already at n = 1.  This records the exact obstruction to the requested
positive level; no 0-level substitution is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1237PositiveLevelObstruction

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Exact obstruction: no `sourceLevel : I.family.index → Nat` can be
invariant under ind1/ind2 and satisfy `ind3 n` adds `n`. -/
theorem no_positive_sourceLevel
    (sourceLevel : I.family.index → Nat)
    (h1 : ∀ (g : ℤ) (c : I.family.index),
      sourceLevel (sourceInd1 I g c) = sourceLevel c)
    (h2 : ∀ (g : ℤ) (c : I.family.index),
      sourceLevel (sourceInd2 I g c) = sourceLevel c)
    (h3 : ∀ (n : Nat) (c : I.family.index),
      sourceLevel (sourceInd3 I n c) = sourceLevel c + n) : False := by
  let c : I.family.index := I.indexOf 0 0
  have hI3 : sourceInd3 I 1 c = I.indexOf 1 0 := by
    simp [sourceInd3, translatePerm, I.translate_theater, c]
  have hI1 : sourceInd1 I (-1) c = I.indexOf 1 0 := by
    simp [sourceInd1, horizontalPerm, I.horizontal_shift_theater, c]
  have hA := h1 (-1) c
  have hB := h3 1 c
  rw [hI1] at hA
  rw [hI3] at hB
  omega

/-- The base-point equality that forces the obstruction. -/
theorem base_ind1_eq_ind3 :
    sourceInd1 I (-1) (I.indexOf 0 0) =
      sourceInd3 I 1 (I.indexOf 0 0) := by
  rw [show sourceInd1 I (-1) (I.indexOf 0 0) = I.indexOf 1 0 by
    simp [sourceInd1, horizontalPerm, I.horizontal_shift_theater]]
  simp [sourceInd3, translatePerm, I.translate_theater]

end LeanFormal.IUT.XiFPaper.S1237PositiveLevelObstruction

end
