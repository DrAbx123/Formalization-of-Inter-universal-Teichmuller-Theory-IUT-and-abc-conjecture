/- U-C: hcond assembly (paper-faithful TripodalDictionary from Legendre support data).

Reuse/recon: david `Mzk1ULHcondChainActual` (`LegendreTpdSupport.perPlace_bound`,
`hcond_after_absorb`, 00:48:16); our `Mzk1ULLegendreSupportDataActual.legendreSupportIncl`
(12:33:06); `Mzk1ULLegendreTripodalEqActual.{twoTorsionXOf_legendre,
legendre_tripodalAdjoin_eq_FtpdLam}` (11:29:35); the paper-faithful
`Mzk1ULTripodalDictionaryPaperActual.{logConductorTpd, tripodalDictionaryOfConductorPaper}`
(11:57:32); RHS `Mzk1ULPointConductorActual.pointND`.  No duplicate infrastructure.

The hcond content splits into: (i) per-place numbers `LogFtpd`/`LogPointND`/`Log2` and
`perPlace_bound` (david's LegendreTpdSupport - the numeric obligation), (ii) the
identification of `D.logFtpd` with the paper conductor `logConductorTpd` and of
`D.logPointND + D.log2Const` with `pointND` (the f_P/[Q(lam):Q] alignment).
This file assembles (i)+(ii) into the dictionary; it introduces no new condition
beyond the documented obligations.
-/
import tmp.sheaf.xif.paper.Mzk1ULTripodalDictionaryPaperActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreSupportDataActual
import tmp.sheaf.xif.paper.Mzk1ULLegendreTripodalEqActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHcondAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHcondChainActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual

variable {K_V : Type*} [Field K_V] [NumberField K_V]

/-- hcond from one LegendreTpdSupport block: the numeric per-place bound plus the
identification of its two entries with the paper conductor and N_D. -/
theorem hcond_of_legendreTpdSupport (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ)) (lam : K_V)
    (D : LegendreTpdSupport)
    (hFtpd : D.logFtpd = logConductorTpd σ hσ badPairs lam)
    (hPoint : D.logPointND + D.log2Const = pointND lam) :
    logConductorTpd σ hσ badPairs lam ≤ pointND lam := by
  rw [← hFtpd, ← hPoint]
  exact D.perPlace_bound

/-- assembly: the paper-faithful TripodalDictionary from per-lambda Legendre support
data whose numeric bounds and identifications are supplied per lambda. -/
noncomputable def tripodalDictionaryOfLegendreSupport (σ : K_V →+* ℂ)
    (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))
    (badPairs : ∀ lam : K_V, Finset (ℕ × ℕ))
    (D : ∀ lam : K_V, LegendreTpdSupport)
    (hFtpd : ∀ lam : K_V, (D lam).logFtpd = logConductorTpd σ hσ badPairs lam)
    (hPoint : ∀ lam : K_V, (D lam).logPointND + (D lam).log2Const = pointND lam)
    (d : ℕ) (eStar : K_V → ℝ) (Cd : ℝ) (heStar : ∀ lam : K_V, eStar lam ≤ Cd) :
    LeanFormal.IUT.XiFPaper.G1D2InterfaceActual.TripodalDictionary K_V d :=
  tripodalDictionaryOfConductorPaper σ hσ badPairs d eStar Cd heStar
    (fun lam => hcond_of_legendreTpdSupport σ hσ badPairs lam (D lam)
      (hFtpd lam) (hPoint lam))

end LeanFormal.IUT.XiFPaper.Mzk1ULHcondAssemblyActual
end
