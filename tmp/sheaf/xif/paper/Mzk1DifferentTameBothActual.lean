import LeanFormal/IUT/IUTIV/Estimates/DifferentTameEquality
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1DifferentTameBothActual — IUT IV Prop 1.3(i): tame equality implies both bounds

Genuine new consumer: in the tame case, the normalized-different equality of
Prop 1.3(i) yields the equality and its ≤ direction as a conjunction.  Reuses the
tree theorem iutIVProp13i_normalizedDifferent_eq_of_tame.
No paper object is claimed beyond the tree theorem; no closure; gate NOT PASSED;
registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DifferentTameBothActual

open LeanFormal.IUT.IUTIV.Estimates

theorem iutIVProp13i_tame_both (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [IsTorsionFree A B] [IsTorsionFree A C] [IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [DecidableEq (Ideal B)] [DecidableEq (Ideal C)]
    (p : Ideal A) (Q : Ideal B) (P : Ideal C) [p.IsPrime] [Q.IsMaximal] [P.IsMaximal]
    (hp : p ≠ ⊥) (hQ : Q ≠ ⊥) (hP : P ≠ ⊥) [Q.LiesOver p] [P.LiesOver Q] [P.LiesOver p]
    [Algebra.IsSeparable (B ⧸ Q) (C ⧸ P)]
    (htame : ((ramificationIdx' Q P : ℕ) : B ⧸ Q) ≠ 0) :
    (((normalizedFactors (differentIdeal A B)).count Q : ℝ) / ramificationIdx' p Q +
        ((ramificationIdx' Q P : ℝ) - 1) / ramificationIdx' p P ≤
      ((normalizedFactors (differentIdeal A C)).count P : ℝ) / ramificationIdx' p P) ∧
    (((normalizedFactors (differentIdeal A C)).count P : ℝ) / ramificationIdx' p P =
      ((normalizedFactors (differentIdeal A B)).count Q : ℝ) / ramificationIdx' p Q +
        ((ramificationIdx' Q P : ℝ) - 1) / ramificationIdx' p P) := by
  have heq := iutIVProp13i_normalizedDifferent_eq_of_tame A B C p Q P hp hQ hP htame
  exact ⟨le_of_eq heq, heq⟩

end LeanFormal.IUT.XiFPaper.Mzk1DifferentTameBothActual

end
