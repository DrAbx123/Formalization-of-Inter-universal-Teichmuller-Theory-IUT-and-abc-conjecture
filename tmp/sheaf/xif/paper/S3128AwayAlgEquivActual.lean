import tmp.sheaf.xif.paper.S3128FixedSubringAlgebraActual
import tmp.sheaf.xif.paper.S3128AwayActionActual
import tmp.sheaf.xif.paper.S3128AwayActionHomAttempt
import tmp.sheaf.xif.paper.S3128LocalAffineQuotientActual
import tmp.sheaf.xif.paper.S3128IsLocalizationAwayActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128AwayAlgEquivActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt
open LeanFormal.IUT.XiFPaper.S3128FixedSubringAlgebraActual
open LeanFormal.IUT.XiFPaper.S3128IsLocalizationAwayActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G] [Fintype G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- Identification of the fixed subring of A_f with the localization of A^G at N_f. -/
noncomputable def S3128AwayFixedAlgEquiv
    (f : A) (hf : forall g : G, g • f = f)
    (hcard : IsUnit (Fintype.card G : A)) :
    letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
    letI := S3128FixedSubringAlgebra (A := A)
      (B := Localization.Away f) (algebraMap A (Localization.Away f))
      (fun g a => (S3128Away_smul_algebraMap (G := G) (A := A) f hf g a).symm)
    S3128FixedSubring G (Localization.Away f) ≃ₐ[S3128FixedSubring G A]
      Localization.Away (S3128NfInv (G := G) (A := A) f) := by
  letI := S3128FixedSubringAlgebra (A := A)
    (B := Localization.Away f) (algebraMap A (Localization.Away f))
    (fun g a => (S3128Away_smul_algebraMap (G := G) (A := A) f hf g a).symm)
  have hcomp : algebraMap (S3128FixedSubring G A)
      (S3128FixedSubring G (Localization.Away f)) =
      S3128FixedSubringMap (G := G) (A := A) (B := Localization.Away f)
        (algebraMap A (Localization.Away f))
        (fun g a => (S3128Away_smul_algebraMap (G := G) (A := A) f hf g a).symm) :=
    S3128FixedSubringAlgebra_algebraMap _ _
  have hloc : IsLocalization.Away (S3128NfInv (G := G) (A := A) f)
      (S3128FixedSubring G (Localization.Away f)) :=
    S3128IsLocalizationAway_NfInv (G := G) (A := A) (B := Localization.Away f)
      (fun g a => S3128Away_smul_algebraMap (G := G) (A := A) f hf g a)
      hcomp hcard f
  exact IsLocalization.algEquiv
    (Submonoid.powers (S3128NfInv (G := G) (A := A) f))
    (S3128FixedSubring G (Localization.Away f))
    (Localization.Away (S3128NfInv (G := G) (A := A) f))

#check S3128AwayFixedAlgEquiv

end LeanFormal.IUT.XiFPaper.S3128AwayAlgEquivActual
end