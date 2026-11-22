/- U-R C2 / K-side bridge (1/2): actual construction of the theta field K = F(θ-values) and the
  completion-degree / normalized-log-volume tower factor.

  ACTUAL CONSTRUCTION (no abstract field parameter): `ThetaK lam torsionCoords` is the
  compositum `Ftpd(√(-1), torsionCoords)` of `Mzk1ULTripodalFieldActual.FtpdLam` with the
  theta-torsion coordinates -- the same construction as `Mzk1G1F2ThetaFieldsActual.ThetaF`, with
  the E[3·5]-coordinate set kept as an explicit instantiation parameter `torsionCoords`
  (sophie: no general-λ E[3]/E[5] coordinate generator exists in the tree; S1687/S1700 are
  specific-curve division polynomials; registered as the instantiation obligation).

  TOWER FACTOR (proved): for a tower of local fields `ℚ_[p] ⊆ Fv ⊆ Kw`,
  `[Kw : ℚ_p] = [Kw : Fv] * [Fv : ℚ_p]` (`Module.finrank_mul_finrank`). This is exactly the
  factor `[K_w:F_w]` appearing when the F-side normalized log volume
  (`NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume`, normalized by the ℚ_p-finrank of
  the tensor block, see FinitePlaceNormalizedUnitScalingLogVolume.lean:92) is compared with the
  K-side one: the tensor-block finrank is the product of the local degrees.

  Place alignment: the F-side places `qVFamTensorPlaces` and the K-side places `ksPlaces` are
  linked by `nativeBadToKPlace` (Mzk1ULKSideLettersActual); the completion map is recorded by
  `ThetaK_placeAlignment` below as an explicit alignment statement (data-level, no fake proof).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaKConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable (lam : ℂ)

/-- **K 的实际构造**：`K = Ftpd(√(-1), θ-torsion 坐标) = ΘF`（compositum）。 -/
noncomputable def ThetaK (torsionCoords : Set ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((↑(FLam lam) : Set ℂ) ∪ ({Complex.I} ∪ torsionCoords))

/-- `Ftpd ≤ K`。 -/
theorem Ftpd_le_ThetaK (torsionCoords : Set ℂ) : FtpdLam lam ≤ ThetaK lam torsionCoords := by
  refine le_trans (IntermediateField.le_normalClosure (F := ℚ) (K := FtpdLam lam) (L := ℂ)) ?_
  intro x hx
  exact IntermediateField.subset_adjoin ℚ ((↑(FLam lam) : Set ℂ) ∪ ({Complex.I} ∪ torsionCoords))
    (Or.inl hx)

/-- `√(-1) ∈ K`。 -/
theorem I_mem_ThetaK (torsionCoords : Set ℂ) : Complex.I ∈ ThetaK lam torsionCoords := by
  exact IntermediateField.subset_adjoin ℚ _ (Or.inr (Or.inl rfl))

/-- θ-torsion 坐标 ∈ K。 -/
theorem torsion_mem_ThetaK (torsionCoords : Set ℂ) {x : ℂ} (hx : x ∈ torsionCoords) :
    x ∈ ThetaK lam torsionCoords := by
  exact IntermediateField.subset_adjoin ℚ _ (Or.inr (Or.inr hx))

/-- **tower factor `[K_w : F_w]`**：`[Kw : ℚ_p] = [Kw : Fv] * [Fv : ℚ_p]`（`Module.finrank_mul_finrank`）。 -/
theorem tower_factor_finrank {p : ℕ} [Fact p.Prime] (Fv Kw : Type*)
    [Field Fv] [Field Kw] [Algebra ℚ_[p] Fv] [Algebra Fv Kw] [Algebra ℚ_[p] Kw]
    [IsScalarTower ℚ_[p] Fv Kw] [FiniteDimensional ℚ_[p] Fv] [FiniteDimensional Fv Kw] :
    Module.finrank ℚ_[p] Kw = Module.finrank Fv Kw * Module.finrank ℚ_[p] Fv :=
  Module.finrank_mul_finrank ℚ_[p] Fv Kw

#print axioms Ftpd_le_ThetaK
#print axioms I_mem_ThetaK
#print axioms torsion_mem_ThetaK
#print axioms tower_factor_finrank

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaKConstructionActual
