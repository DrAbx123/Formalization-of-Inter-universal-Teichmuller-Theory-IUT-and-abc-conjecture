/- H-T F3 s^Q input, route 8.2.

Reused donors (查重结论):
* LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual.sQOf
* LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual.log_sQOf_eq
  (DONE 2026-11-16T23:55:17, axioms propext/Classical.choice/Quot.sound)
No new sQ object is defined here; the existing donor is re-exported under the
name expected by the F3/Q-side interface, and the F3 generic data
(Mzk1HTF3ConductorHeightActual.TruncatedConductorHeightData) is connected to it.
-/
import tmp.sheaf.xif.paper.Mzk1ULTripodalConductorActual
import tmp.sheaf.xif.paper.Mzk1HTF3ConductorHeightActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F3SQInputActual

open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual
open LeanFormal.IUT.XiFPaper.Mzk1HTF3ConductorHeightActual

/-- F3 s^Q input: the log of the product of the bad primes is the sum of their logs.
This is david's DONE `log_sQOf_eq`, re-exported under the name used by the F3
Q-side assembly. -/
theorem log_sQ_eq_sum_log (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) :
    Real.log (sQOf S : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) :=
  log_sQOf_eq S hS

/-- Positivity of the donor product, used to rewrite `log (sQ)` in the F3 assembly. -/
theorem sQ_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) : (0 : ℝ) < (sQOf S : ℝ) :=
  sQOf_pos S hS

/-- The F3 generic sum bound with the s^Q log input: if the per-place weights are
`logResidue i = log (p i)` for a finite family of nonzero primes, then the
weighted conductor sum is bounded by the height sum plus card * C. -/
theorem truncatedConductorHeight_le_height_add_const_sQ {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, p i ≠ 0)
    (D : TruncatedConductorHeightData ι)
    (hlog : ∀ i, D.logResidue i = Real.log (p i : ℝ)) :
    (∑ i, (D.conductorExponent i : ℝ) * D.logResidue i)
      ≤ (∑ i, D.localHeight i) + (Fintype.card ι : ℝ) * D.C :=
  truncatedConductorHeight_le_height_add_const D

#print axioms log_sQ_eq_sum_log
#print axioms truncatedConductorHeight_le_height_add_const_sQ
end LeanFormal.IUT.XiFPaper.Mzk1G1F3SQInputActual
