import tmp.sheaf.xif.paper.S2449ResidueAlgClosedAPI
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationSubring
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442ResidueAction
namespace LeanFormal.IUT.XiFPaper.S2450ResidueIsAlgClosedActual
variable (p : Nat) [Fact (Nat.Prime p)]
local notation "V" => PadicValuationSubring p
local notation "K" => PadicAlgCl p
theorem S2450_residue_isAlgClosed : IsAlgClosed (PadicResidueField p) := by
  apply IsAlgClosed.of_exists_root
  intro f hf_monic hf_irred
  have hf_deg : f.natDegree ≠ 0 :=
    Nat.ne_of_gt (Irreducible.natDegree_pos hf_irred)
  have hlift : f ∈ Polynomial.lifts (IsLocalRing.residue V) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact IsLocalRing.residue_surjective (f.coeff n)
  obtain ⟨q, hq_map, hq_deg, hq_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlift hf_monic
  let qK : Polynomial K := q.map (algebraMap V K)
  have hqK_deg : qK.degree ≠ 0 := by
    rw [show qK = q.map (algebraMap V K) from rfl,
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective V K), hq_deg]
    exact (Polynomial.degree_pos_of_irreducible hf_irred).ne'
  obtain ⟨x, hx_root⟩ := IsAlgClosed.exists_root qK hqK_deg
  have hx_int : IsIntegral V x := by
    apply IsIntegral.of_aeval_monic hq_monic
    · rw [Polynomial.natDegree_eq_of_degree_eq hq_deg]
      exact hf_deg
    · have hzero : Polynomial.eval₂ (algebraMap V K) x q = 0 := by
        have h := hx_root
        rw [Polynomial.IsRoot] at h
        change (Polynomial.map (algebraMap V K) q).eval x = 0 at h
        rw [Polynomial.eval_map] at h
        exact h
      change IsIntegral V (Polynomial.eval₂ (algebraMap V K) x q)
      rw [hzero]
      exact isIntegral_zero
  obtain ⟨v, hv⟩ := (IsIntegrallyClosed.isIntegral_iff (x := x)).mp hx_int
  refine ⟨IsLocalRing.residue V v, ?_⟩
  change f.eval (IsLocalRing.residue V v) = 0
  rw [← hq_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hqeval0 : q.eval v = 0 := by
    apply IsFractionRing.injective V K
    rw [map_zero]
    have hlink : qK.eval x = algebraMap V K (q.eval v) := by
      change (Polynomial.map (algebraMap V K) q).eval x =
        algebraMap V K (q.eval v)
      rw [Polynomial.eval_map, ← hv, Polynomial.eval₂_at_apply]
    have hqeval : algebraMap V K (q.eval v) = 0 := by
      rw [← hlink]
      have h := hx_root
      rw [Polynomial.IsRoot] at h
      exact h
    simpa using hqeval
  rw [hqeval0, map_zero]

theorem S2450S2448ResidueAlgClosed :
    LeanFormal.IUT.XiFPaper.S2448ResidueFrobeniusAPI.S2448ResidueAlgClosedRequired p :=
  S2450_residue_isAlgClosed p
/-- Surjectivity of x |-> x^p on the residue field, from algebraic closedness. -/
theorem S2450_frobenius_surjective :
    Function.Surjective (fun x : PadicResidueField p => x ^ p) := by
  haveI : IsAlgClosed (PadicResidueField p) := S2450_residue_isAlgClosed p
  intro y
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.Prime.pos (Fact.out : Nat.Prime p))
  exact ⟨x, hx⟩
#check S2450S2448ResidueAlgClosed
#check S2450_frobenius_surjective
#check S2450_residue_isAlgClosed
end LeanFormal.IUT.XiFPaper.S2450ResidueIsAlgClosedActual
end
