/- Θ-data instantiation (1/n): the number fields Fmod / Ftpd / F for the Legendre parameter.

  RECON (per Lead): `Mzk1ULTripodalFieldActual` already defines
    * `jOfLam (lam) = 256 (1 - lam + lam^2)^3 / (lam^2 (1 - lam)^2)`,
    * `FmodLam lam = adjoin Q {jOfLam lam}`,
    * `FtpdLam lam = adjoin Q {jOfLam lam, lam}`,
    * `FLam lam = normalClosure Q ↥(FtpdLam lam) C`.
  Also available: `Mzk1ULSArFtpdIdentityActual.FtpdLam_eq_adjoin_lam` (lam generates Ftpd),
  `Mzk1ULLegendreTripodalEqActual.{legendre_tripodalAdjoin, legendre_tripodalAdjoin_eq_FtpdLam}`.
 
  The full field `F = Ftpd(sqrt(-1), E[15]-torsion)` is packaged as `ThetaF lam torsionCoords`
  where `torsionCoords` is the set of coordinates of a generating set of E[15]-torsion. NO
  general-lambda E[3]/E[5]/E[15] COORDINATE GENERATOR is in the tree: `S1687Torsion23Realization`
  and `S1700ThreeTorsionExhaustion` provide division-polynomial realisations for specific curves,
  `Mzk1IutIVProp14TorsionActual` is a cardinality statement, and the Legendre files give only
  2-torsion coordinates. Hence `torsionCoords` is an EXPLICIT OBLIGATION parameter here (its
  instantiation with the division-polynomial roots of psi_3, psi_5 is the next task, to be
  coordinated with sophie); we do NOT fake it.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import tmp.sheaf.xif.paper.Mzk1ULSArFtpdIdentityActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreTripodalEqActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaFieldsActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSArFtpdIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTripodalEqActual

variable (lam : ℂ)

/-- `Fmod = Q(j(lam))`（定义即 `FmodLam`）。 -/
theorem Fmod_eq_adjoin : FmodLam lam = IntermediateField.adjoin ℚ ({jOfLam lam} : Set ℂ) :=
  rfl

/-- `Ftpd = Q(j(lam), lam)`（定义即 `FtpdLam`）。 -/
theorem Ftpd_eq_adjoin :
    FtpdLam lam = IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ) := rfl

/-- `Fmod ≤ Ftpd`。 -/
theorem Fmod_le_Ftpd : FmodLam lam ≤ FtpdLam lam := by
  rw [Fmod_eq_adjoin, Ftpd_eq_adjoin]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  apply IntermediateField.subset_adjoin ℚ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  exact Or.inl hx

/-- `Ftpd ≤ FLam`（`FLam` 是 `Ftpd` 的正规闭包）。 -/
theorem Ftpd_le_FLam : FtpdLam lam ≤ FLam lam := by
  unfold FLam
  exact IntermediateField.le_normalClosure (F := ℚ) (K := FtpdLam lam) (L := ℂ)

/-- **Θ-域**：`F = Ftpd(√(-1), torsionCoords)`（`torsionCoords` = E[15]-torsion 坐标，显式义务）。 -/
noncomputable def ThetaF (torsionCoords : Set ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((↑(FLam lam) : Set ℂ) ∪ ({Complex.I} ∪ torsionCoords))

/-- `Ftpd ≤ ΘF`。 -/
theorem Ftpd_le_ThetaF (torsionCoords : Set ℂ) : FtpdLam lam ≤ ThetaF lam torsionCoords := by
  refine le_trans (Ftpd_le_FLam lam) ?_
  unfold ThetaF
  intro x hx
  exact IntermediateField.subset_adjoin ℚ
    ((↑(FLam lam) : Set ℂ) ∪ ({Complex.I} ∪ torsionCoords)) (Or.inl hx)

/-- `I ∈ ΘF`。 -/
theorem I_mem_ThetaF (torsionCoords : Set ℂ) : Complex.I ∈ ThetaF lam torsionCoords := by
  unfold ThetaF
  exact IntermediateField.subset_adjoin ℚ
    ((↑(FLam lam) : Set ℂ) ∪ ({Complex.I} ∪ torsionCoords))
    (Or.inr (Or.inl rfl))

#print axioms Fmod_le_Ftpd
#print axioms Ftpd_le_FLam
#print axioms Ftpd_le_ThetaF
#print axioms I_mem_ThetaF

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaFieldsActual