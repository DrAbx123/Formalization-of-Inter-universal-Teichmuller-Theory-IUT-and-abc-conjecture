import tmp.sheaf.xif.paper.S3128BasicOpenLocalizationUnitActual
import tmp.sheaf.xif.paper.S3128SurjExistsActual
import tmp.sheaf.xif.paper.S3128ExistsOfEqActual
import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128IsLocalizationAwayActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenLocalizationUnitActual
open LeanFormal.IUT.XiFPaper.S3128SurjExistsActual
open LeanFormal.IUT.XiFPaper.S3128ExistsOfEqActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B] [Algebra A B]
  [Algebra (S3128FixedSubring G A) (S3128FixedSubring G B)]

/-- The fixed subring of B is the localization of the fixed subring of A at N_f. -/
theorem S3128IsLocalizationAway_NfInv
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm))
    (hcard : IsUnit (Fintype.card G : A))
    (f : A) [IsLocalization.Away f B] :
    IsLocalization.Away
      (S3128NfInv (G := G) (A := A) f)
      (S3128FixedSubring G B) :=
  IsLocalization.Away.mk (S3128NfInv (G := G) (A := A) f)
    (S3128NfInv_image_isUnit (G := G) (A := A) (B := B)
      halg hcomp)
    (S3128Surj_actual (G := G) (A := A) (B := B)
      halg hcomp hcard f)
    (S3128ExistsOfEq (G := G) (A := A) (B := B)
      halg hcomp f)


/-- The localization map on fixed subrings is an open immersion. -/
theorem S3128SpecFixedMap_isOpenImmersion
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm))
    (hcard : IsUnit (Fintype.card G : A))
    (f : A) [IsLocalization.Away f B] :
    IsOpenImmersion
      (S3128SpecFixedMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm)) := by
  haveI := S3128IsLocalizationAway_NfInv (G := G) (A := A) (B := B)
    halg hcomp hcard f
  have h := IsOpenImmersion.of_isLocalization
    (R := S3128FixedSubring G A) (S := S3128FixedSubring G B)
    (S3128NfInv (G := G) (A := A) f)
  rw [S3128SpecFixedMap, ← hcomp]
  exact h

#check S3128SpecFixedMap_isOpenImmersion

#check S3128IsLocalizationAway_NfInv

end LeanFormal.IUT.XiFPaper.S3128IsLocalizationAwayActual
end