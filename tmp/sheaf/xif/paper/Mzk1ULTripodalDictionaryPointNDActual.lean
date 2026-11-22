import tmp.sheaf.xif.paper.Mzk1ULTripodalDictionarySigmaFreeActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import tmp.sheaf.xif.paper.Mzk1G1D2InterfaceActual
import Mathlib.Tactic

/-! Point-ND version of the tripodal dictionary producer.

The D2 interface field fFtpd_le_conductor is stated with the point-field conductor
pointND (K := K_V) lam, which differs from the K_V-level truncConductor used by the
older wrapper tripodalDictionaryOfConductor'.  Hence this file builds the dictionary
directly (no alias) with the pointND-typed conductor input.
-/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryPointNDActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionarySigmaFreeActual

/-- The pointND-conductor version of the tripodal dictionary producer. -/
noncomputable def tripodalDictionaryOfConductorND {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (S_bad : Finset ℕ) (d : ℕ) (eStar : K_V → ℝ) (Cd : ℝ)
    (heStar : ∀ lam : K_V, eStar lam ≤ Cd)
    (hcond : ∀ lam : K_V, Real.log (fFtpd' σ S_bad lam)
      ≤ LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual.pointND (K := K_V) lam) :
    LeanFormal.IUT.XiFPaper.G1D2InterfaceActual.TripodalDictionary K_V d where
  logDiff := logDiff' σ
  dFtpd := dFtpd' σ
  fFtpd := fFtpd' σ S_bad
  dmod := d
  eStar := eStar
  Cd := Cd
  dFtpd_pos := fun lam => dFtpd'_pos σ lam
  fFtpd_pos := fun lam => fFtpd'_pos σ S_bad lam
  logDiff_eq := fun lam => logDiff'_eq σ lam
  fFtpd_le_conductor := hcond
  dmod_le := le_rfl
  eStar_le := heStar

#print axioms tripodalDictionaryOfConductorND
end LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryPointNDActual
