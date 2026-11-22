/- H-T F3 (route 8.2, L719-760): generic truncated-conductor-height interface.

Paper: N_{E_i}(y) is the (truncated) conductor height of the elliptic curve E_i
evaluated at the point y; the F3 statement is N_{E_i}(y) <= h_{E_i}(y) + C_i
(truncated conductor height vs intersection height).  Per-place form used in the
route: at each place v of the base, N_v <= h_v + c_v, and a finite sum gives the
extra Sum c_v.  This file is the GENERIC interface/epsilon: the actual per-place
data (E_i, the truncated conductor exponents, the local intersection heights) is
supplied later by the H-T assembly (grace's B3 E_phi object), not here.

NOTE: `Mzk1G1LocalHeightCriterionActual.truncConductor` is the D1 truncated
conductor (a different object); it is NOT claimed to be paper's N_{E_i} and is
not used here.  When instantiating, document the identification explicitly.

Consumer: H-T F1-F8 assembly (andrew's P8-P); instantiate with the actual E_i/phi_i
objects once available.

TODO (pending david's IV.txt extraction): `log_sQ_eq_sum_log`
(`Real.log (Prod P in badFPrimeSet, (underIntGen P).natAbs) = Sum log p_P`)
will be added in the D2/Q-side file once the sQ support/truncation convention is
confirmed from IUT-TEXT L1540-1575.  Do not define the sQ object before that.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1HTF3ConductorHeightActual

/-- generic truncated-conductor-height data (H-T F3, route 8.2): per-place
computed conductor contributions, per-place intersection heights, and the uniform
per-place constant, with the local F3 bound. -/
structure TruncatedConductorHeightData (ι : Type*) [Fintype ι] where
  /-- per-place (truncated) conductor contribution N_v -/
  conductorExponent : ι → ℕ
  /-- per-place intersection height h_{E_i,v} -/
  localHeight : ι → ℝ
  /-- per-place weight log p_v -/
  logResidue : ι → ℝ
  /-- uniform per-place constant C_i -/
  C : ℝ
  /-- the per-place F3 bound N_v <= h_v + C -/
  local_bound : ∀ i, (conductorExponent i : ℝ) * logResidue i ≤ localHeight i + C

/-- PROVED: the finite sum form of F3, N <= h + (card) C (generic). -/
theorem truncatedConductorHeight_le_height_add_const {ι : Type*} [Fintype ι]
    (D : TruncatedConductorHeightData ι) :
    (∑ i, (D.conductorExponent i : ℝ) * D.logResidue i)
      ≤ (∑ i, D.localHeight i) + (Fintype.card ι : ℝ) * D.C := by
  calc (∑ i, (D.conductorExponent i : ℝ) * D.logResidue i)
      ≤ ∑ i, (D.localHeight i + D.C) := Finset.sum_le_sum (fun i _ => D.local_bound i)
    _ = (∑ i, D.localHeight i) + (Fintype.card ι : ℝ) * D.C := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp [Finset.card_univ]

end LeanFormal.IUT.XiFPaper.Mzk1HTF3ConductorHeightActual
end
