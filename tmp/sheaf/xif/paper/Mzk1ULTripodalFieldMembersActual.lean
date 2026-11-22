/- U-C: tripodal-field membership facts (batch item (3): support the Legendre
equality lemmas that David will port from LANA GlobalField).

check list: `FmodLam lam = Q(j(lam))`, `FtpdLam lam = Q(j(lam), lam)`, and the
membership facts j(lam), lam in FtpdLam lam plus FmodLam <= FtpdLam.  For the
Legendre model the 2-torsion x-coordinates are 0, 1, lam and j in Q(lam), so
F_tpd = Q(lam) = FtpdLam (see Lead/David ruling 2026-11-17).
-/
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldMembersActual

open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual

variable (lam : ℂ)

/-- PROVED (definitional): FmodLam is the adjoin of j(lam) alone. -/
theorem FmodLam_eq_adjoin : FmodLam lam = IntermediateField.adjoin ℚ ({jOfLam lam} : Set ℂ) := rfl

/-- PROVED (definitional): FtpdLam is the adjoin of j(lam) and lam. -/
theorem FtpdLam_eq_adjoin :
    FtpdLam lam = IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ) := rfl

/-- PROVED: j(lam) lies in the tripodal field. -/
theorem jOfLam_mem_FtpdLam : jOfLam lam ∈ FtpdLam lam := by
  rw [FtpdLam_eq_adjoin]
  exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- PROVED: lam itself lies in the tripodal field. -/
theorem lam_mem_FtpdLam : lam ∈ FtpdLam lam := by
  rw [FtpdLam_eq_adjoin]
  exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- PROVED: FmodLam is a subfield of FtpdLam. -/
theorem FmodLam_le_FtpdLam : FmodLam lam ≤ FtpdLam lam := by
  rw [FmodLam_eq_adjoin, FtpdLam_eq_adjoin]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact IntermediateField.subset_adjoin ℚ _ (by simp)

end LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldMembersActual
end
