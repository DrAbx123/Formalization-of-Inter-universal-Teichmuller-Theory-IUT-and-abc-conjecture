import tmp.sheaf.n8.closure.EtaIntegralStructureS

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaIntegralProperActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSRoute

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- The production integral log-shell is not the whole local field: it is
compact, while the p-adic field is noncompact. -/
theorem integralLogShell_ne_univ :
    (integralLogShell (K := ℚ_[l.value]) (p := l.value) :
      Set ℚ_[l.value]) ≠ Set.univ := by
  intro h
  have hcompact : IsCompact (Set.univ : Set ℚ_[l.value]) := by
    rw [← h]
    exact isCompact_integralLogShell (K := ℚ_[l.value]) (p := l.value)
  haveI : CompactSpace ℚ_[l.value] := isCompact_univ_iff.mp hcompact
  exact (not_compactSpace_iff.mpr
    (inferInstance : NoncompactSpace ℚ_[l.value])) ‹CompactSpace ℚ_[l.value]›

/-- Actual properness: some p-adic point is outside the production
integral log-shell. -/
theorem etaIntegral_proper_actual :
    ∃ x : ℚ_[l.value], x ∉ (etaIntegralStructureS l).integral := by
  by_contra h
  push_neg at h
  apply integralLogShell_ne_univ (l := l)
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rw [← etaIntegralStructureS_integral_eq]
  exact h x

end LeanFormal.IUT.N8Closure.EtaIntegralProperActual
