/- R5 bridge: from unconditional monogenic integers to per-M minpoly data (AlgEquiv, retry).

Reuse: Mzk1G1UniversalMonogenicIntegersActual.nonempty_monogenicIntegers,
Mzk1G1UniversalMonogenicLocalActual.adjoin_eq_top_of_fractionRing,
IntermediateField.adjoin.finrank.
-/
import tmp.sheaf.xif.paper.Mzk1G1UniversalMonogenicIntegersActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalMonogenicLocalActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Tactic
noncomputable section
open Polynomial IntermediateField
namespace LeanFormal.IUT.XiFPaper.Mzk1G1MonogenicMinpolyBridgeActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalMonogenicIntegersActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalMonogenicLocalActual

variable {p : Nat} [Fact p.Prime]
variable {M : Type*} [NormedField M] [CharZero M] [CompleteSpace M] [IsUltrametricDist M]
  [ProperSpace M] [NormedAlgebra ℚ_[p] M] [FiniteDimensional ℚ_[p] M]

/-- Per-M monogenic generator data: x : M integral, norm <= 1, M = Q_p(x), and
minpoly degree equals the field degree. -/
theorem exists_minpoly_data :
    ∃ (x : M) (e : M ≃ₐ[ℚ_[p]]
      IntermediateField.adjoin ℚ_[p] ({x} : Set M)),
      IsIntegral ℚ_[p] x ∧ ‖x‖ ≤ 1 ∧
      (minpoly ℚ_[p] x).natDegree = Module.finrank ℚ_[p] M := by
  obtain ⟨Mmono⟩ := nonempty_monogenicIntegers (p := p) (L := M)
  let x : M := algebraMap (Integers M) M Mmono.x
  have hxint : IsIntegral ℚ_[p] x := IsIntegral.of_finite ℚ_[p] x
  have hxnorm : ‖x‖ ≤ 1 := Mmono.x.property
  have htop : (⊤ : IntermediateField ℚ_[p] M) =
      IntermediateField.adjoin ℚ_[p] ({x} : Set M) := by
    have h := adjoin_eq_top_of_fractionRing (p := p) (L := M) Mmono.x Mmono.adjoin_top
    exact (IntermediateField.adjoin_eq_top_of_algebra (F := ℚ_[p]) (S := ({x} : Set M)) h).symm
  let e : M ≃ₐ[ℚ_[p]] IntermediateField.adjoin ℚ_[p] ({x} : Set M) :=
    (IntermediateField.topEquiv (F := ℚ_[p]) (E := M)).symm.trans
      (IntermediateField.equivOfEq htop)
  have hdeg : (minpoly ℚ_[p] x).natDegree = Module.finrank ℚ_[p] M := by
    rw [← IntermediateField.adjoin.finrank (K := ℚ_[p]) (x := x) hxint]
    exact e.toLinearEquiv.finrank_eq.symm
  exact ⟨x, e, hxint, hxnorm, hdeg⟩

#print axioms exists_minpoly_data
end LeanFormal.IUT.XiFPaper.Mzk1G1MonogenicMinpolyBridgeActual
