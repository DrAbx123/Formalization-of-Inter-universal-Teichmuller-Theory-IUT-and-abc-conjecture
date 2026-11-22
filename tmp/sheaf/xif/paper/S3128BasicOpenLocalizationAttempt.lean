import tmp.sheaf.xif.paper.S3128BasicOpenQuotientActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128BasicOpenLocalizationAttempt

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G] [Fintype G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]
  [Algebra A B] {f : A} [IsLocalization.Away f B]
  [Algebra (S3128FixedSubring G A) (S3128FixedSubring G B)]
  (halg : forall (g : G) (a : A),
    g • algebraMap A B a = algebraMap A B (g • a))
  (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
    S3128FixedSubringMap (G := G) (A := A) (B := B)
      (algebraMap A B) (fun g a => (halg g a).symm))

example : IsLocalization.Away
    (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
      (S3128NfInv (G := G) (A := A) f))
    (S3128FixedSubring G B) :=
  IsLocalization.Away.mk _ ?_ ?_ ?_

end LeanFormal.IUT.XiFPaper.S3128BasicOpenLocalizationAttempt
end