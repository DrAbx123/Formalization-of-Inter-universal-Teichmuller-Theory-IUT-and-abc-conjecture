import tmp.sheaf.xif.paper.S3128FixedSubringAlgebraActual
import tmp.sheaf.xif.paper.S3128IsLocalizationAwayActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128AwayFixedAlgEquivActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128FixedSubringAlgebraActual
open LeanFormal.IUT.XiFPaper.S3128IsLocalizationAwayActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- Identification of the fixed subring of A_f with the localization of A^G at N_f,
with the required instances supplied explicitly. -/
noncomputable def S3128AwayFixedAlgEquiv
    (f : A) (hcard : IsUnit (Fintype.card G : A))
    [Algebra A (Localization.Away f)]
    [IsLocalization.Away f (Localization.Away f)]
    [MulSemiringAction G (Localization.Away f)]
    (halg : forall (g : G) (a : A),
      g • algebraMap A (Localization.Away f) a =
        algebraMap A (Localization.Away f) (g • a))
    [Algebra (S3128FixedSubring G A) (S3128FixedSubring G (Localization.Away f))]
    (hcomp : algebraMap (S3128FixedSubring G A)
        (S3128FixedSubring G (Localization.Away f)) =
      S3128FixedSubringMap (G := G) (A := A) (B := Localization.Away f)
        (algebraMap A (Localization.Away f)) (fun g a => (halg g a).symm)) :
    S3128FixedSubring G (Localization.Away f) ≃ₐ[S3128FixedSubring G A]
      Localization.Away (S3128NfInv (G := G) (A := A) f) := by
  haveI : IsLocalization.Away (S3128NfInv (G := G) (A := A) f)
      (S3128FixedSubring G (Localization.Away f)) :=
    S3128IsLocalizationAway_NfInv (G := G) (A := A) (B := Localization.Away f)
      halg hcomp hcard f
  exact IsLocalization.algEquiv
    (Submonoid.powers (S3128NfInv (G := G) (A := A) f))
    (S3128FixedSubring G (Localization.Away f))
    (Localization.Away (S3128NfInv (G := G) (A := A) f))

#check S3128AwayFixedAlgEquiv

end LeanFormal.IUT.XiFPaper.S3128AwayFixedAlgEquivActual
end