import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace S1895MonoidProbe

open LeanFormal.IUT

local instance fivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

def negOne : LocalIntegralMonoid 5 :=
  ⟨-1, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩

theorem negOne_ne_one : negOne ≠ (1 : LocalIntegralMonoid 5) := by
  intro h
  have h' : (-1 : LocalAlgebraicIntegerRing 5) = 1 := congrArg Subtype.val h
  norm_num at h'

theorem negOne_mul_self : negOne * negOne = (1 : LocalIntegralMonoid 5) := by
  apply Subtype.ext
  change (-1 : LocalAlgebraicIntegerRing 5) * (-1) = 1
  ring

theorem valueMonoid_sq_eq_one {x : SourceHaarActualValueMonoid} (h : x * x = 1) : x = 1 := by
  have h' : Multiplicative.toAdd x + Multiplicative.toAdd x = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  apply Multiplicative.ext
  apply Subtype.ext
  have hreal : ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) +
      ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) = 0 := by
    exact congrArg (fun z : sourceHaarActualNonpositiveAddSubmonoid => (z : Real)) h'
  linarith

theorem no_monoid_equiv :
    ¬ Nonempty (LocalIntegralMonoid 5 ≃* SourceHaarActualValueMonoid) := by
  rintro ⟨e⟩
  have h := congrArg (fun x => e x) negOne_mul_self
  rw [map_mul, map_one] at h
  have hy : e negOne = 1 := valueMonoid_sq_eq_one h
  have h1 : negOne = 1 := by
    calc
      negOne = e.symm (e negOne) := (e.symm_apply_apply negOne).symm
      _ = e.symm 1 := by rw [hy]
      _ = 1 := map_one e.symm
  exact negOne_ne_one h1

end S1895MonoidProbe