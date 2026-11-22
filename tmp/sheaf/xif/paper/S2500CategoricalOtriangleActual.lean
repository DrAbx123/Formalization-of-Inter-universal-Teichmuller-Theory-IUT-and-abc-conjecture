import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitEvaluationImage
import tmp.sheaf.xif.paper.S2490LiteralOProObstructionActual

/-! # S2500: minimal O^◃/O^▷ and universal-cover pro-system data

Actual local carriers: O^◃ = LocalIntegralMonoid p (nonzero integral closure),
O^▷ candidate = its unit group, with the actual evaluated-unit equivalence.
The categorical universal-covering pro-object, its transition monoid homs, the
O^▷ submonoid/pro-generators and rho_v maps are recorded as exact missing data;
Mathlib has no pro-object category API for this.  No fake universal cover. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.LocalIntegralMonoid
open LeanFormal.IUT.XiFPaper.S2490LiteralOProObstructionActual

namespace LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Actual O^◃ carrier: the nonzero integral-closure monoid. -/
abbrev S2500ODiamond : Type := LocalIntegralMonoid p

/-- Actual O^▷ candidate: the unit group of O^◃. -/
abbrev S2500OTriangle : Type := (LocalIntegralMonoid p)ˣ

/-- The actual evaluated-unit subgroup of the algebraic closure units. -/
abbrev S2500EvaluatedUnits : Subgroup (AlgebraicClosure ℚ_[p])ˣ :=
  evaluatedUnitSubgroup p

/-- The actual evaluation map from O^▷ to the closure units, with image in the
evaluated-unit subgroup. -/
noncomputable def S2500UnitEvaluation :
    S2500OTriangle p →* S2500EvaluatedUnits p :=
  unitEvaluationToImage p

theorem S2500UnitEvaluation_injective :
    Function.Injective (S2500UnitEvaluation p) :=
  unitEvaluationToImage_injective p

theorem S2500UnitEvaluation_surjective :
    Function.Surjective (S2500UnitEvaluation p) :=
  unitEvaluationToImage_surjective p

/-- Minimal categorical pro-system data (index, transition monoid homs).
No inhabitant is asserted; this is the missing pro-object specification. -/
structure S2500ProSystem where
  Index : Type
  le : Index → Index → Prop
  le_refl : ∀ i, le i i
  le_trans : ∀ {i j k}, le i j → le j k → le i k
  obj : Index → Type
  transition : ∀ {i j}, le i j → obj j → obj i
  transition_refl : ∀ i (x : obj i),
    transition (le_refl i) x = x


/-- Exact missing: a universal-covering pro-system mapping to O^◃, with the
O^▷ submonoid at each finite level and compatible transition homs. -/
structure S2500UniversalCoverRequired where
  proSystem : S2500ProSystem
  toODiamond : ∀ i, proSystem.obj i → S2500ODiamond p
  oTriangleSubmonoid : ∀ i, Set (proSystem.obj i)
  oTriangleGenerator : ∀ i, proSystem.obj i
  oTriangleGenerator_mem :
    ∀ i, oTriangleGenerator i ∈ oTriangleSubmonoid i
  generator_compat : ∀ {i j} (h : proSystem.le i j),
    proSystem.transition h (oTriangleGenerator j) = oTriangleGenerator i

/-- Exact missing rho_v realified maps on the pro-generators. -/
structure S2500RhoVRequired where
  rho : S2500OTriangle p → Real
  rho_one : rho 1 = 0
  rho_mul : ∀ x y, rho (x * y) = rho x + rho y

#check S2500ODiamond
#check S2500OTriangle
#check S2500UnitEvaluation
#check S2500UniversalCoverRequired
#check S2500RhoVRequired

end LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual
end
