/- R3a (4/n): the theta field as an actual compositum Ftpd + torsion coordinates (no normal
  closure shortcut, no abstract field parameter).

  K := Ftpd(√(-1), E[3], E[5], E[l]) with the torsion coordinates realized by the division
  polynomial root sets of `Mzk1G1F2ThetaTorsionCoordsActual.threeTorsionX` and
  `Mzk1G1F2ThetaTorsionFiveActual.fiveTorsionX`/`legendreΨn` (actual multiplication kernels).
  This corrects the earlier `ThetaF`/`ThetaK` (which used the normal closure of FLam): the
  normal closure is replaced here by the explicit adjoin of the torsion coordinate sets.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaTorsionCoordsActual
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaTorsionFiveActual
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaDivisionPolynomialsActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCompositumActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionCoordsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionFiveActual

variable (lam : ℂ) (l : ℕ)

/-- `l`-torsion x-coordinates of the Legendre curve (actual preΨ_l roots). -/
noncomputable def lTorsionX (lam : ℂ) (l : ℕ) : Set ℂ :=
  {x : ℂ | (legendreΨn lam (l : ℤ)).eval x = 0}

/-- **θ-域的实际构造**：`K = adjoin ℚ (Ftpd ∪ {√(-1)} ∪ E[3] ∪ E[5] ∪ E[l] 的 x-坐标)`。 -/
noncomputable def ThetaCompositum (lam : ℂ) (l : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((↑(FtpdLam lam) : Set ℂ) ∪
    ({Complex.I} ∪ (threeTorsionX lam ∪ (fiveTorsionX lam ∪ lTorsionX lam l))))

/-- `Ftpd ≤ K`。 -/
theorem Ftpd_le_ThetaCompositum : FtpdLam lam ≤ ThetaCompositum lam l := by
  intro x hx
  exact IntermediateField.subset_adjoin ℚ _ (Or.inl hx)

/-- `√(-1) ∈ K`。 -/
theorem I_mem_ThetaCompositum : Complex.I ∈ ThetaCompositum lam l :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr (Or.inl rfl))

/-- E[3] 的 x-坐标 ∈ K。 -/
theorem threeTorsionX_subset_ThetaCompositum {x : ℂ} (hx : x ∈ threeTorsionX lam) :
    x ∈ ThetaCompositum lam l :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr (Or.inr (Or.inl hx)))

/-- E[5] 的 x-坐标 ∈ K。 -/
theorem fiveTorsionX_subset_ThetaCompositum {x : ℂ} (hx : x ∈ fiveTorsionX lam) :
    x ∈ ThetaCompositum lam l :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr (Or.inr (Or.inr (Or.inl hx))))

/-- E[l] 的 x-坐标 ∈ K。 -/
theorem lTorsionX_subset_ThetaCompositum {x : ℂ} (hx : x ∈ lTorsionX lam l) :
    x ∈ ThetaCompositum lam l :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr (Or.inr (Or.inr (Or.inr hx))))

#print axioms Ftpd_le_ThetaCompositum
#print axioms I_mem_ThetaCompositum
#print axioms threeTorsionX_subset_ThetaCompositum
#print axioms fiveTorsionX_subset_ThetaCompositum
#print axioms lTorsionX_subset_ThetaCompositum

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCompositumActual
