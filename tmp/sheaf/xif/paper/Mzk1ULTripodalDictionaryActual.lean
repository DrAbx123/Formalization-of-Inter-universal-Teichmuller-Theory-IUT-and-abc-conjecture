/- U-C: TripodalDictionary field-level constructions (D1b interface).

`G1D2InterfaceActual.TripodalDictionary (K) (d)` is a statement-level interface
(route 6.4 / L613-621) with fields logDiff, dFtpd, fFtpd, dmod, eStar, Cd and the
relations logDiff_eq, fFtpd_le_conductor, dmod_le, eStar_le.  This file builds the
actual per-lambda objects on the tripodal field `FtpdLam (σ lam)` (Mzk1ULTripodalFieldActual).

Per Lead ruling: `dmod := d` is the D1 quantifier degree bound ([F_mod:Q] <= d),
documented as the upper-bound convention (not the actual per-lambda degree, which
needs a T); eStar/Cd are supplied at the T-wrapper layer.

STATUS: the constructions logDiff/dFtpd/fFtpd (and their positivity/logDiff_eq
relations) are built here.  The field `fFtpd_le_conductor` is a REAL inequality
(conductor at each place <= truncated conductor N_D(lambda), route L617-621); it
needs the per-place conductor/s^Q data (see the explicit gap list) and is NOT
claimed here -- so no inhabitant of TripodalDictionary is asserted.
-/
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import tmp.sheaf.xif.paper.Mzk1ULFtpdNumberFieldActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1G1D2InterfaceActual
import tmp.sheaf.xif.paper.Mzk1G1LocalHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.ULTripodalNumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual

variable {K_V : Type*} [Field K_V] [NumberField K_V] (σ : K_V →+* ℂ)
variable (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
variable (S_bad : Finset ℕ)

/-- the tripodal field of the point λ (intermediate field of C). -/
abbrev FtpdField (lam : K_V) : Type := ↥(FtpdLam (σ lam))

/-- actual log-different of the tripodal field (paper log d_Ftpd). -/
noncomputable def logDiff (lam : K_V) : ℝ := by
  letI := numberField_FtpdLam (σ lam) (hσ lam)
  exact logDifferentF (FtpdLam (σ lam))

/-- actual root discriminant of the tripodal field (paper d_Ftpd). -/
noncomputable def dFtpd (lam : K_V) : ℝ := by
  letI := numberField_FtpdLam (σ lam) (hσ lam)
  exact NumberField.rootDiscr (FtpdLam (σ lam))

/-- actual conductor exponential of the tripodal field (paper f_Ftpd). -/
noncomputable def fFtpd (lam : K_V) : ℝ := by
  letI := numberField_FtpdLam (σ lam) (hσ lam)
  exact Real.exp (logConductorF (FtpdLam (σ lam)) S_bad)

/-- PROVED: logDiff = log d_Ftpd (definitional, paper route L617). -/
theorem logDiff_eq (lam : K_V) : logDiff σ hσ lam = Real.log (dFtpd σ hσ lam) := by
  unfold logDiff dFtpd
  letI := numberField_FtpdLam (σ lam) (hσ lam)
  rfl

/-- PROVED: d_Ftpd > 0 (root discriminant >= 1). -/
theorem dFtpd_pos (lam : K_V) : 0 < dFtpd σ hσ lam := by
  unfold dFtpd
  letI := numberField_FtpdLam (σ lam) (hσ lam)
  exact lt_of_lt_of_le zero_lt_one (Mzk1ULPaperLettersActual.one_le_rootDiscr _)

/-- PROVED: f_Ftpd > 0 (it is an exponential). -/
theorem fFtpd_pos (lam : K_V) : 0 < fFtpd σ hσ S_bad lam := Real.exp_pos _



/-- the TripodalDictionary inhabitant assembled from the actual per-lambda objects;
the only substantive input is the per-place conductor inequality hcond (route L617-621).
`dmod := d` is the D1 degree-bound convention; eStar/Cd are supplied at the T layer. -/
noncomputable def tripodalDictionaryOfConductor
    (d : ℕ) (eStar : K_V → ℝ) (Cd : ℝ)
    (heStar : ∀ lam : K_V, eStar lam ≤ Cd)
    (hcond : ∀ lam : K_V, Real.log (fFtpd σ hσ S_bad lam)
      ≤ LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual.pointND lam) :
    LeanFormal.IUT.XiFPaper.G1D2InterfaceActual.TripodalDictionary K_V d where
  logDiff := logDiff σ hσ
  dFtpd := dFtpd σ hσ
  fFtpd := fFtpd σ hσ S_bad
  dmod := d
  eStar := eStar
  Cd := Cd
  dFtpd_pos := fun lam => dFtpd_pos σ hσ lam
  fFtpd_pos := fun lam => fFtpd_pos σ hσ S_bad lam
  logDiff_eq := fun lam => logDiff_eq σ hσ lam
  fFtpd_le_conductor := hcond
  dmod_le := le_rfl
  eStar_le := heStar


end LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual
end