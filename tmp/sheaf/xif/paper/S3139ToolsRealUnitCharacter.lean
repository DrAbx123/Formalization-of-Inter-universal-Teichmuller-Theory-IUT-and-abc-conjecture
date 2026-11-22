import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139 tool: multiplicative Real unit character from a realified degree hom

Reusable mathematical tool (not a paper object): any monoid homomorphism from a
group into the multiplicative additive group `Multiplicative R` (the realified
degree channel of a valuation/log) yields a multiplicative character into the
real units `R^x` by exponentiating its additive value.

This packages the construction used for the finite-place copy scalar
(`S3139C2LocalDegreeDataActual.SourceFmodLocalElementMap.localScalarUnit`) in a
generic, stream-independent form so any valuation/log-degree channel can use it.

No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ToolsRealUnitCharacter

universe u

variable {G : Type u} [Group G]

/-- The real unit character associated to a realified degree homomorphism: the
copy degree in `Multiplicative R` becomes a positive real scalar. -/
noncomputable def realUnitCharacterOfMultiplicative
    (f : G →* Multiplicative ℝ) : G →* ℝˣ where
  toFun g := Units.mk0 (Real.exp (Multiplicative.toAdd (f g)))
    (ne_of_gt (Real.exp_pos _))
  map_one' := by
    apply Units.ext
    show Real.exp (Multiplicative.toAdd (f 1)) = 1
    rw [map_one]
    simp
  map_mul' := by
    intro a b
    apply Units.ext
    show Real.exp (Multiplicative.toAdd (f (a * b))) =
      Real.exp (Multiplicative.toAdd (f a)) *
        Real.exp (Multiplicative.toAdd (f b))
    rw [map_mul]
    have h : Multiplicative.toAdd (f a * f b) =
        Multiplicative.toAdd (f a) + Multiplicative.toAdd (f b) := rfl
    rw [h, Real.exp_add]

/-- The real unit character of the unit copy is the unit. -/
theorem realUnitCharacterOfMultiplicative_one
    (f : G →* Multiplicative ℝ) :
    realUnitCharacterOfMultiplicative f 1 = 1 :=
  map_one (realUnitCharacterOfMultiplicative f)

/-- The real unit character is multiplicative. -/
theorem realUnitCharacterOfMultiplicative_mul
    (f : G →* Multiplicative ℝ) (a b : G) :
    realUnitCharacterOfMultiplicative f (a * b) =
      realUnitCharacterOfMultiplicative f a *
        realUnitCharacterOfMultiplicative f b :=
  map_mul (realUnitCharacterOfMultiplicative f) a b

end LeanFormal.IUT.XiFPaper.S3139ToolsRealUnitCharacter

end
