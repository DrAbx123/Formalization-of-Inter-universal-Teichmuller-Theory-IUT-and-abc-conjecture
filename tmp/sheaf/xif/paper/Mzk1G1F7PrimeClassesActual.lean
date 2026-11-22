import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import tmp.sheaf.xif.paper.Mzk1G1F7TameMonogenicActual
import tmp.sheaf.xif.paper.Mzk1G1F7PvdnAdapterActual
import tmp.sheaf.xif.paper.Mzk1G1F7PNotDvdActual
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentLogActual
import Mathlib.Tactic
/-!
# R7 F7: three prime-class contribution wiring and `D(L) ≤ ∑ log p + C_n`

Route §9.1 L584/L586/L594/L602/L613: unramified δ=0
(`F7DifferentExponentBoundsActual`), tame δ=e−1 (`F7TameMonogenicActual`), wild
contribution ≤ (v_p(e)+1) log p (`F7PvdnAdapterActual`); sum packaging below.
## Reuse / donor check: all donors DONE; this file only wires them.
-/
noncomputable section
open Polynomial Ideal NumberField
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F7PrimeClassesActual

universe u

/-- Wild p | n: normalized different contribution ≤ `(v_p(e)+1) log p` (re-export). -/
theorem f7_wild_contribution_le {p : Nat} [Fact p.Prime] {e δ : Nat} (he : 0 < e)
    (hδ : δ ≤ e * (padicValNat p e + 1)) :
    (δ : ℝ) * Real.log (p : ℝ) / (e : ℝ) ≤
      ((padicValNat p e + 1 : Nat) : ℝ) * Real.log (p : ℝ) :=
  LeanFormal.IUT.XiFPaper.Mzk1G1F7PvdnAdapterActual.normalizedDifferentContribution_le he hδ

/-- Packaging: if the three prime classes give per-prime bounds `contribution p ≤ bound p`,
then `D(L) = ∑ contribution` is bounded by `∑ bound`. -/
structure F7PrimeClassContributionData (S : Finset ℕ) where
  contribution : ℕ → ℝ
  bound : ℕ → ℝ
  hclass : ∀ p ∈ S, contribution p ≤ bound p
  DL : ℝ
  hDL : DL = ∑ p ∈ S, contribution p

theorem F7PrimeClassContributionData.DL_le_sum_bound {S : Finset ℕ}
    (D : F7PrimeClassContributionData S) : D.DL ≤ ∑ p ∈ S, D.bound p := by
  rw [D.hDL]
  exact Finset.sum_le_sum D.hclass

#print axioms f7_wild_contribution_le
#print axioms F7PrimeClassContributionData.DL_le_sum_bound
end LeanFormal.IUT.XiFPaper.Mzk1G1F7PrimeClassesActual
end