import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3138: actual source procession core from the original input

Rebuilds the *source-level* parameterized procession kernel of IUT III Theorem
3.11 from a genuine `OriginalInput`: the finite Q(i)-at-5 model (`concreteInput`)
is no longer the only inhabitant of the Step XI parameter objects.

* `SourceStepXILabel := ZZ x ZZ` is the paper's lattice of `(n,m)` indices;
* `SourceStepXIChoice := I.family.index x NN` pairs a genuine family index with
  the vertical level coordinate used by every in-tree procession model;
* `sourceStepXICore`: Ind1/Ind2 are the actual lattice translations
  `I.translate` of the original input, Ind3 shifts the level coordinate.

The Ind laws are closed by the actual `I.translate` algebra (associativity,
inverse, and the two lattice commutations); no field is a placeholder.  The
level coordinate is the repo's modeling of the Ind3 height (same shape as the
finite `ProcessionChoice`), not an identification with a paper object.

Source: IUT III Theorem 3.11 (procession/Ind1-Ind3); IUT II (Theta packets).
Consumer: `S3138SourceProcessionProfileActual` and `S3138SourceStepXIActual`.
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Label, choice, and base of the source procession -/

/-- The label type of the source procession: the actual lattice coordinates
`(n,m)` of the original input. -/
abbrev SourceStepXILabel : Type := ℤ × ℤ

/-- The choice type of the source procession: the actual family index of the
original input together with the vertical level coordinate. -/
abbrev SourceStepXIChoice (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Type ui :=
  I.family.index × ℕ

/-- The source base choice: the family index of `(0,0)` at level zero. -/
abbrev SourceStepXIBase (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceStepXIChoice I :=
  (I.indexOf 0 0, 0)

/-- The coordinate representative of a family index. -/
theorem sourceStepXI_indexOf_indexEquiv
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (i : I.family.index) :
    I.indexOf (I.index_equiv i).1 (I.index_equiv i).2 = i :=
  Equiv.symm_apply_apply I.index_equiv i

/-! ## 2. The actual source core (Ind1/Ind2/Ind3) -/

/-- The actual `Core` of the source procession.  The two horizontal operations
are the actual lattice translations of the original input; `ind3` is the
vertical shift of the level coordinate. -/
noncomputable def sourceStepXICore
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Core SourceStepXILabel (SourceStepXIChoice I) where
  base := SourceStepXIBase I
  level c := c.2
  ind1 g c := (I.translate g.1 0 c.1, c.2)
  ind2 g c := (I.translate 0 g.2 c.1, c.2)
  ind3 n c := (c.1, c.2 + n)
  ind1_zero := by
    intro c
    apply Prod.ext
    · exact I.translate_zero c.1
    · rfl
  ind1_add := by
    intro g h c
    apply Prod.ext
    · show I.translate (g + h).1 0 c.1 = I.translate h.1 0 (I.translate g.1 0 c.1)
      rw [I.translate_add]
      rfl
    · rfl
  ind1_inverse := by
    intro g c
    apply Prod.ext
    · show I.translate (-g).1 0 (I.translate g.1 0 c.1) = c.1
      rw [I.translate_add]
      have hneg : (-g).1 = -g.1 := rfl
      rw [hneg, show g.1 + -g.1 = 0 by ring]
      simpa using I.translate_zero c.1
    · rfl
  ind2_zero := by
    intro c
    apply Prod.ext
    · exact I.translate_zero c.1
    · rfl
  ind2_add := by
    intro g h c
    apply Prod.ext
    · show I.translate 0 (g + h).2 c.1 = I.translate 0 h.2 (I.translate 0 g.2 c.1)
      rw [I.translate_add]
      rfl
    · rfl
  ind2_inverse := by
    intro g c
    apply Prod.ext
    · show I.translate 0 (-g).2 (I.translate 0 g.2 c.1) = c.1
      rw [I.translate_add]
      have hneg : (-g).2 = -g.2 := rfl
      rw [hneg, show g.2 + -g.2 = 0 by ring]
      simpa using I.translate_zero c.1
    · rfl
  ind3_zero := by
    intro c
    apply Prod.ext
    · rfl
    · simp
  ind3_add := by
    intro m n c
    apply Prod.ext
    · rfl
    · omega
  ind1_ind2_commute := by
    intro g h c
    apply Prod.ext
    · exact I.translate_commute g.1 0 0 h.2 c.1
    · rfl
  ind1_ind3_commute := by
    intro g n c
    rfl
  ind2_ind3_commute := by
    intro g n c
    rfl
  ind1_level := by
    intro g c
    rfl
  ind2_level := by
    intro g c
    rfl
  ind3_level := by
    intro n c
    omega

end LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual

end
