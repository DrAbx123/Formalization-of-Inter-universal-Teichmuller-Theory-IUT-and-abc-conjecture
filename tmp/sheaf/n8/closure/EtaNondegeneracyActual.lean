import tmp.sheaf.n8.closure.EtaIntegralStructureS
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.EtaRssLogShellLine
import tmp.sheaf.n8.closure.EtaIntegralProperActual
import tmp.sheaf.n8.closure.P6L

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNondegeneracyActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSRoute
open LeanFormal.IUT.N8Closure.P6L
open scoped Padic
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## Actual value-group line guard -/

theorem etaRval_nontrivial : Nontrivial Rval := by
  infer_instance

theorem etaPilot_ne_one : etaPilot X ≠ 1 :=
  EtaValueGroupLineActual.etaPilot_ne_one X

/-! ## Actual Rss carrier guard -/

theorem etaRss_nonempty : Nonempty (EtaRssLogShellLineData X) :=
  ⟨etaRssLogShellLineData X⟩

/-! ## Actual integral-structure guard -/

theorem etaIntegral_nonempty (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] :
    (etaIntegralStructureS l).integral.Nonempty := by
  rw [etaIntegralStructureS_integral_eq]
  exact ⟨0, integers_subset_integralLogShell (K := ℚ_[l.value]) (p := l.value)
    (zero_mem _)⟩

theorem etaIntegral_proper_gap (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] :
    ∃ x : ℚ_[l.value], x ∉ (etaIntegralStructureS l).integral :=
  EtaIntegralProperActual.etaIntegral_proper_actual (l := l)

/-! ## Actual core package -/

/-- Actual nondegeneracy data that can be built from the three ETA
components: Rval/pilot, Rss carri
er, and integral structure. -/
structure EtaNondegeneracyActualCore
    (l : PrimeGeFive) (X : N8NativeInput l) [Fact (Nat.Prime l.value)] where
  line : EtaValueGroupLineData X
  rss : EtaRssLogShellLineData X
  integral : EtaIntegralStructureS l
  rval_nontrivial : Nontrivial Rval
  pilot_ne_one : line.pilot ≠ 1
  integral_nonempty : integral.integral.Nonempty

noncomputable def etaNondegeneracyActualCore (l : PrimeGeFive)
    (X : N8NativeInput l) [Fact (Nat.Prime l.value)] :
    EtaNondegeneracyActualCore l X where
  line := etaValueGroupLineData X
  rss := etaRssLogShellLineData X
  integral := etaIntegralStructureS l
  rval_nontrivial := etaRval_nontrivial
  pilot_ne_one := etaPilot_ne_one X
  integral_nonempty := etaIntegral_nonempty l

theorem etaNondegeneracyActualCore_nonempty (l : PrimeGeFive)
    (X : N8NativeInput l) [Fact (Nat.Prime l.value)] :
    Nonempty (EtaNondegeneracyActualCore l X) :=
  ⟨etaNondegeneracyActualCore l X⟩

/-! ## Exact remaining guards -/

/-- The guards that still require an actual eta comparison: nonzero
Theta, nondegenerate Values, separated reference/region, and a
nonconstant comparison.  They are not instantiated with free data here. -/
structure EtaRemainingGuards (X : N8NativeInput l) where
  theta : ℝ
  theta_ne_zero : theta ≠ 0
  values : Set ℝ
  values_ne_singleton : values ≠ {0}
  reference : GlobalRegion X
  region : GlobalRegion X
  reference_ne_region : reference ≠ region
  comparison : Rval → EtaRssLogShellLineData X
  comparison_nonconstant : ¬ ∃ c : EtaRssLogShellLineData X,
    ∀ x : Rval, comparison x = c

end LeanFormal.IUT.N8Closure.EtaNondegeneracyActual
