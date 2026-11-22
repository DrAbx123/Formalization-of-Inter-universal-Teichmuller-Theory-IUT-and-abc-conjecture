/- U-C: PAPER-FAITHFUL tripodal f_Ftpd (place-weighted conductor) and its dictionary.

Replaces the legacy prime-counted `Mzk1ULTripodalDictionaryActual.fFtpd`
(exp logConductorF, SUPERSEDED / NOT PAPER) by the paper's place-weighted conductor
over the tripodal field (IUT IV L1305-1353 + Def 1.9: log f_K = (Sum f_p log p)/[K:Q]).
The bad support is supplied as (inertia degree, rational prime) pairs; identifying
them with the actual bad places (Legendre discriminant 16 lam^2 (1-lam)^2) is the
remaining support obligation.
-/
import tmp.sheaf.xif.paper.Mzk1ULConductorDegActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalDictionaryActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import tmp.sheaf.xif.paper.Mzk1ULFtpdNumberFieldActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryPaperActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual
open NumberField
open LeanFormal.IUT.XiFPaper.ULTripodalNumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual

variable {K_V : Type*} [Field K_V] [NumberField K_V]

/-- paper-faithful normalized conductor of the tripodal field, from the bad support
given as (inertia degree, rational prime) pairs. -/
noncomputable def logConductorTpd (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ)) (lam : K_V) : ℝ := by
  letI := numberField_FtpdLam (σ lam) (hσ lam)
  exact (∑ q ∈ badPairs lam, ((q.1 : ℝ) * Real.log (q.2 : ℝ))) /
    (Module.finrank ℚ ↥(FtpdLam (σ lam)) : ℝ)

/-- paper-faithful f_Ftpd: exponential of the place-weighted conductor. -/
noncomputable def fFtpdPaper (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ)) (lam : K_V) : ℝ :=
  Real.exp (logConductorTpd σ hσ badPairs lam)

/-- PROVED: log of the paper-faithful f_Ftpd is the place-weighted conductor. -/
theorem log_fFtpdPaper (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ)) (lam : K_V) :
    Real.log (fFtpdPaper σ hσ badPairs lam)
      = logConductorTpd σ hσ badPairs lam := Real.log_exp _

/-- PROVED: the paper-faithful f_Ftpd is positive. -/
theorem fFtpdPaper_pos (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ)) (lam : K_V) :
    0 < fFtpdPaper σ hσ badPairs lam := Real.exp_pos _

/-- the paper-faithful TripodalDictionary: same actual d_Ftpd/log-diff, f_Ftpd the
place-weighted conductor, and hcond against the point-field N_D. -/
noncomputable def tripodalDictionaryOfConductorPaper (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ)) (d : ℕ) (eStar : K_V → ℝ) (Cd : ℝ)
    (heStar : ∀ lam : K_V, eStar lam ≤ Cd)
    (hcond : ∀ lam : K_V, logConductorTpd σ hσ badPairs lam ≤ pointND lam) :
    LeanFormal.IUT.XiFPaper.G1D2InterfaceActual.TripodalDictionary K_V d where
  logDiff := logDiff σ hσ
  dFtpd := dFtpd σ hσ
  fFtpd := fFtpdPaper σ hσ badPairs
  dmod := d
  eStar := eStar
  Cd := Cd
  dFtpd_pos := dFtpd_pos σ hσ
  fFtpd_pos := fFtpdPaper_pos σ hσ badPairs
  logDiff_eq := logDiff_eq σ hσ
  fFtpd_le_conductor := fun lam => by
    rw [log_fFtpdPaper σ hσ badPairs lam]
    exact hcond lam
  dmod_le := le_rfl
  eStar_le := heStar

end LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryPaperActual
end