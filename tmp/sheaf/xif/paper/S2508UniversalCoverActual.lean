import tmp.sheaf.xif.paper.S2503FiniteLevelToODiamondActual
import tmp.sheaf.xif.paper.S2504OTriangleGeneratorsActual

/-! # S2508: actual universal-cover data with the base p as pro-generator

For each finite Galois L, the base uniformizer `p` is an actual nonzero
integral element of the finite-level O^◃ carrier.  Its powers form an actual
O^▷ submonoid, and the S2503 finite-level maps send this generator to itself.
This fills S2500UniversalCoverRequired with actual data (the base p generator,
not a fabricated trivial generator). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual
open LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual
open LeanFormal.IUT.XiFPaper.S2502FiniteLevelODiamondActual
open LeanFormal.IUT.XiFPaper.S2503FiniteLevelToODiamondActual
open LeanFormal.IUT.XiFPaper.S2504OTriangleGeneratorsActual
open scoped nonZeroDivisors

namespace LeanFormal.IUT.XiFPaper.S2508UniversalCoverActual

variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2508_p_mem_base :
    (p : ℚ_[p]) ∈ S2503BaseRing p := by
  rw [S2503BaseRing, Valuation.mem_integer_iff]
  exact (Padic.valuation_p_lt_one (ValuativeRel.valuation ℚ_[p])).le

/-- The base uniformizer p as an element of the finite-level O^◃ carrier. -/
noncomputable def S2508P (L : S2501Index p) :
    S2502ODiamond p L.1 :=
  ⟨⟨algebraMap ℚ_[p] L.1 p, by
      have hx : IsIntegral (S2503BaseRing p)
          (algebraMap (S2503BaseRing p) L.1
            ⟨p, S2508_p_mem_base p⟩) :=
        isIntegral_algebraMap
      simpa [S2503BaseRing] using hx⟩,
    mem_nonZeroDivisors_of_ne_zero (by
      intro h
      have h0 : (algebraMap ℚ_[p] L.1) p = 0 := by
        exact congrArg Subtype.val h
      have hpne : (p : ℚ_[p]) ≠ 0 :=
        by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      exact (algebraMap ℚ_[p] L.1).injective.ne hpne
        (by simpa using h0))⟩

/-- Actual universal-cover data: base p as the generator at every finite level. -/
noncomputable def S2508UniversalCover : S2500UniversalCoverRequired p where
  proSystem := S2503FiniteProSystem p
  toODiamond := fun L => S2503ODiamondMap p L.1
  oTriangleSubmonoid := fun L =>
    (Submonoid.powers (S2508P p L) : Set (S2502ODiamond p L.1))
  oTriangleGenerator := fun L => S2508P p L
  oTriangleGenerator_mem := by
    intro L
    exact Submonoid.mem_powers (S2508P p L)
  generator_compat := by
    intro L M h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

#check S2508UniversalCover

#check S2508P

end LeanFormal.IUT.XiFPaper.S2508UniversalCoverActual
end
