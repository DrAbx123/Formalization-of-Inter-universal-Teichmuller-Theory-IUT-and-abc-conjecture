import tmp.sheaf.xif.paper.S2504OTriangleGeneratorsActual
import tmp.sheaf.xif.paper.S2505RhoVActual
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-! # S2507: exact finite-valuation input for the S2504 generator

The remaining construction of the finite-level generator is exactly a discrete
valuation on L with cyclic/nontrivial value group, whose integer ring is the
S2502 integral closure, plus a uniformizer.  Mathlib supplies
`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`; the missing piece is
the restricted valuation data itself.  No inhabitant is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual
open LeanFormal.IUT.XiFPaper.S2502FiniteLevelODiamondActual
open LeanFormal.IUT.XiFPaper.S2504OTriangleGeneratorsActual
open scoped nonZeroDivisors

namespace LeanFormal.IUT.XiFPaper.S2507FiniteValuationGoal

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact missing finite-level valuation data. -/
structure S2507FiniteValuationData (L : S2501Index p) where
  v : Valuation (L.1) (WithZero (Multiplicative ℤ))
  [rankOneDiscrete : v.IsRankOneDiscrete]
  uniformizer : v.integer
  isUniformizer : v.IsUniformizer uniformizer
  integer_eq : v.integer = S2502IntegralClosure p L.1

/-- The uniformizer gives an actual element of the finite-level O^◃ carrier. -/
noncomputable def S2507Generator
    {L : S2501Index p} (D : S2507FiniteValuationData p L) :
    S2502ODiamond p L.1 := by
  letI : D.v.IsRankOneDiscrete := D.rankOneDiscrete
  exact
    ⟨⟨(D.uniformizer : L.1), by
        rw [← D.integer_eq]
        exact D.uniformizer.2⟩,
      mem_nonZeroDivisors_of_ne_zero (by
        intro h
        exact D.isUniformizer.ne_zero (congrArg Subtype.val h))⟩

#check S2507FiniteValuationData
#check S2507Generator

end LeanFormal.IUT.XiFPaper.S2507FiniteValuationGoal
end
