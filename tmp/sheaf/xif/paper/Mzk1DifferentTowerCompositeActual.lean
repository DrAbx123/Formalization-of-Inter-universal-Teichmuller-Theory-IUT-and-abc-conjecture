import LeanFormal/IUT/IUTIV/Estimates/DifferentTowerEstimate
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1DifferentTowerCompositeActual — Prop 1.3(i) tower multiplicity + inequality composite

Genuine composite of the existing IUT IV Prop 1.3(i) tower assets: the exact
multiplicity identity for the different in a Dedekind tower and the normalized
different inequality hold together.  No new paper input; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DifferentTowerCompositeActual

open LeanFormal.IUT.IUTIV.Estimates
open Ideal UniqueFactorizationMonoid Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem iutIVProp13i_tower_composite (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [IsTorsionFree A B] [IsTorsionFree A C] [IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [DecidableEq (Ideal B)] [DecidableEq (Ideal C)]
    (p : Ideal A) (Q : Ideal B) (P : Ideal C) [p.IsPrime] [Q.IsPrime] [P.IsPrime]
    (hp : p ≠ ⊥) (hQ : Q ≠ ⊥) (hP : P ≠ ⊥) [Q.LiesOver p] [P.LiesOver Q] [P.LiesOver p] :
    ((normalizedFactors (differentIdeal A C)).count P =
        (normalizedFactors (differentIdeal B C)).count P +
          ramificationIdx' Q P * (normalizedFactors (differentIdeal A B)).count Q) ∧
      (((normalizedFactors (differentIdeal A B)).count Q : ℝ) / ramificationIdx' p Q +
          ((ramificationIdx' Q P : ℝ) - 1) / ramificationIdx' p P ≤
        ((normalizedFactors (differentIdeal A C)).count P : ℝ) / ramificationIdx' p P) :=
  ⟨count_differentIdeal_tower A B C Q P hQ hP,
   iutIVProp13i_normalizedDifferent_ge A B C p Q P hp hQ hP⟩

end LeanFormal.IUT.XiFPaper.Mzk1DifferentTowerCompositeActual

end
