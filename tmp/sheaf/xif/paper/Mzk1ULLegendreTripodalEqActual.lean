/- U-C: Legendre 2-torsion x-coordinates and the tripodal-field identification.

For E_lam: y^2 = x (x-1) (x-lam), the 2-torsion x-coordinates are {0, 1, lam}
(y = 0, P+P = 0) and j(E_lam) = j(lam); hence F_tpd = F_mod(E[2]) = Q(j, lam) = Q(lam).
Uses david's per-point bridges (Mzk1ULLegendreTwoTorsionActual) and the LANA-port
tripodalFieldOf (Mzk1ULTripodalConductorActual); the Legendre API is
LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve.
-/
import tmp.sheaf.xif.paper.Mzk1ULLegendreTwoTorsionActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldMembersActual
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTripodalEqActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldMembersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTwoTorsionActual
open WeierstrassCurve

variable (lam : ℂ) [(legendreWeierstrassCurve lam).IsElliptic]
variable (htwo : (2 : ℂ) ≠ 0) (h0 : lam ≠ 0) (h1 : lam ≠ 1)

/-- PROVED: (0,0) is nonsingular for the Legendre curve. -/
theorem legendre_nonsingular_zero (h0 : lam ≠ 0) :
    (legendreWeierstrassCurve lam).toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · rw [legendreWeierstrassCurve_equation_iff]
    ring
  · left
    simp only [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂,
      legendreWeierstrassCurve_a₄]
    intro h
    apply h0
    linear_combination -h

/-- PROVED: (1,0) is nonsingular for the Legendre curve. -/
theorem legendre_nonsingular_one (h1 : lam ≠ 1) :
    (legendreWeierstrassCurve lam).toAffine.Nonsingular 1 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · rw [legendreWeierstrassCurve_equation_iff]
    ring
  · left
    simp only [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂,
      legendreWeierstrassCurve_a₄]
    intro h
    have hsimp : -(3 + 2 * (-(1 + lam)) + lam) = 0 := by simpa using h
    have hlin : lam - 1 = 0 := by linear_combination hsimp
    exact h1 (sub_eq_zero.mp hlin)

/-- PROVED: (lam,0) is nonsingular for the Legendre curve. -/
theorem legendre_nonsingular_lam (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (legendreWeierstrassCurve lam).toAffine.Nonsingular lam 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · rw [legendreWeierstrassCurve_equation_iff]
    ring
  · left
    simp only [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂,
      legendreWeierstrassCurve_a₄]
    intro h
    have hquad : lam ^ 2 - lam = 0 := by linear_combination -h
    have hmul : lam * (lam - 1) = 0 := by
      have hre : lam * (lam - 1) = lam ^ 2 - lam := by ring
      rw [hre]; exact hquad
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h0 h'
    · exact h1 (sub_eq_zero.mp h')

/-- PROVED: twoTorsionXOf of the Legendre curve is {0,1,lam}. -/
theorem twoTorsionXOf_legendre (lam : ℂ) [(legendreWeierstrassCurve lam).IsElliptic]
    (htwo : (2 : ℂ) ≠ 0) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    twoTorsionXOf ℂ (legendreWeierstrassCurve lam) = ({0, 1, lam} : Set ℂ) := by
  ext a
  constructor
  · rintro ⟨b, hns, hmem⟩
    have hb : b = 0 := by
      by_contra hbne
      exact legendre_not_mem_twoTorsion_of_y_ne lam htwo hns hbne hmem
    subst hb
    have h' : (0 : ℂ) ^ 2 = a * (a - 1) * (a - lam) := by
      exact (legendreWeierstrassCurve_equation_iff lam a 0).mp hns.1
    have heq : (a * (a - 1)) * (a - lam) = 0 := by
      linear_combination -h'
    rcases mul_eq_zero.mp heq with hA | hC
    · rcases mul_eq_zero.mp hA with h0' | h1'
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl h0'
      · have ha1 : a = 1 := sub_eq_zero.mp h1'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inl ha1)
    · have hal : a = lam := sub_eq_zero.mp hC
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr hal)
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with haz | hao | hal
    · rw [haz]
      exact ⟨0, legendre_nonsingular_zero lam h0,
        legendre_mem_twoTorsion_of_x lam 0 (legendre_nonsingular_zero lam h0)⟩
    · rw [hao]
      exact ⟨0, legendre_nonsingular_one lam h1,
        legendre_mem_twoTorsion_of_x lam 1 (legendre_nonsingular_one lam h1)⟩
    · rw [hal]
      exact ⟨0, legendre_nonsingular_lam lam h0 h1,
        legendre_mem_twoTorsion_of_x lam lam (legendre_nonsingular_lam lam h0 h1)⟩

/- NOTE: david's `tripodalFieldOf F E` requires `[NumberField F]`, while our working
ambient field is ℂ (not a NumberField), so we state the identification for the
unfolded adjoin over ℂ; the FtpdLam equality below is what the consumers use. -/

/-- PROVED: the unfolded F_tpd of the Legendre curve is Q(j(lam), lam). -/
theorem legendre_tripodalAdjoin (lam : ℂ)
    [(legendreWeierstrassCurve lam).IsElliptic] (htwo : (2 : ℂ) ≠ 0)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    IntermediateField.adjoin ℚ (insert (legendreWeierstrassCurve lam).j
        (twoTorsionXOf ℂ (legendreWeierstrassCurve lam)))
      = IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ) := by
  rw [twoTorsionXOf_legendre lam htwo h0 h1, legendre_j_eq_jOfLam lam htwo h0 h1]
  have hset : ((insert (jOfLam lam) (insert (0 : ℂ) (insert (1 : ℂ) ({lam} : Set ℂ))))
      : Set ℂ) = insert (jOfLam lam) (insert (0 : ℂ) (insert (1 : ℂ) ({lam} : Set ℂ))) := rfl
  rw [hset]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact IntermediateField.subset_adjoin ℚ _ (by simp)
    · simpa using IntermediateField.algebraMap_mem
        (IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ)) (0 : ℚ)
    · simpa using IntermediateField.algebraMap_mem
        (IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ)) (1 : ℚ)
    · exact IntermediateField.subset_adjoin ℚ _ (by simp)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact IntermediateField.subset_adjoin ℚ _ (by simp)
    · exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- PROVED: the unfolded F_tpd of the Legendre curve equals FtpdLam. -/
theorem legendre_tripodalAdjoin_eq_FtpdLam (lam : ℂ)
    [(legendreWeierstrassCurve lam).IsElliptic] (htwo : (2 : ℂ) ≠ 0)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    IntermediateField.adjoin ℚ (insert (legendreWeierstrassCurve lam).j
        (twoTorsionXOf ℂ (legendreWeierstrassCurve lam))) = FtpdLam lam := by
  rw [legendre_tripodalAdjoin lam htwo h0 h1, FtpdLam_eq_adjoin]

end LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTripodalEqActual