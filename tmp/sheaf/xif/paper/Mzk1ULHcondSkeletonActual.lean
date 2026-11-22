/- U-C: hcond skeleton (same-domain support/truncation interface, intermediate).

The final TripodalDictionary field `fFtpd_le_conductor` (now with pointND, david's
semantic correction 23:16) is packaged here as the named statement HcondStatement
and fed into the assembly `tripodalDictionaryOfConductor`.  The per-place support /
truncation proof is NOT provided here: it is David's Legendre/support chain
(`twoTorsionXOf_legendre`, `tripodalFieldOf_legendre_eq_adjoin`, bad-place inclusion
with the log 2 constant).  This file is an INTERFACE + assembly bridge; no
inequality is asserted.
-/
import tmp.sheaf.xif.paper.Mzk1ULTripodalDictionaryActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHcondSkeletonActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual

variable {K_V : Type*} [Field K_V] [NumberField K_V]
variable (σ : K_V →+* ℂ) (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam)) (S_bad : Finset ℕ)

/-- the hcond statement (paper L617-621) with N_D on the point field (pointND). -/
def HcondStatement : Prop :=
  ∀ lam : K_V, Real.log (fFtpd σ hσ S_bad lam) ≤ pointND lam

/-- PROVED: the statement is the pointwise relation. -/
theorem hcondStatement_iff :
    HcondStatement σ hσ S_bad ↔
      ∀ lam : K_V, Real.log (fFtpd σ hσ S_bad lam) ≤ pointND lam := Iff.rfl

/-- the TripodalDictionary assembled from the actual objects and hcond. -/
noncomputable def tripodalDictionary_of_hcond (d : ℕ) (eStar : K_V → ℝ) (Cd : ℝ)
    (heStar : ∀ lam : K_V, eStar lam ≤ Cd)
    (h : HcondStatement σ hσ S_bad) :
    LeanFormal.IUT.XiFPaper.G1D2InterfaceActual.TripodalDictionary K_V d :=
  tripodalDictionaryOfConductor σ hσ S_bad d eStar Cd heStar h

end LeanFormal.IUT.XiFPaper.Mzk1ULHcondSkeletonActual
end
