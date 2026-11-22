import tmp.sheaf.xif.paper.S3128SurjExistsActual
import tmp.sheaf.xif.paper.S3128SurjProductActual
import tmp.sheaf.xif.paper.S3128BasicOpenLocalizationUnitActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128ExistsOfEqActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SurjHtermActual
open LeanFormal.IUT.XiFPaper.S3128SurjProductActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B] [Algebra A B]
  [Algebra (S3128FixedSubring G A) (S3128FixedSubring G B)]

/-- The equalizer condition for the localization at NInv. -/
theorem S3128ExistsOfEq
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm))
    (f : A) [IsLocalization.Away f B]
    (a b : S3128FixedSubring G A)
    (hab : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) a =
      algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) b) :
    exists n : Nat,
      (S3128NfInv (G := G) (A := A) f) ^ n * a =
        (S3128NfInv (G := G) (A := A) f) ^ n * b := by
  have hsub : forall x : S3128FixedSubring G A,
      (S3128FixedSubring G B).subtype
        (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) x) =
        algebraMap A B (x : A) := by
    intro x
    rw [hcomp]
    simp [S3128FixedSubringMap]
  have hB : algebraMap A B (a : A) = algebraMap A B (b : A) := by
    have h := congrArg (S3128FixedSubring G B).subtype hab
    rwa [hsub a, hsub b] at h
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers f) hB
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff c.val f).mp c.property
  have hc' : (f ^ m : A) * (a : A) = f ^ m * (b : A) := by
    simpa [← hm] using hc
  let P : A := S3128SurjP (G := G) (A := A) f m
  have hNpow : (S3128Nf (G := G) f) ^ m = f ^ m * P := by
    rw [S3128Nf]
    rw [← Finset.prod_pow]
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset G))
      (f := fun g => (g • f) ^ m) (a := 1) (Finset.mem_univ 1)]
    simp [P, S3128SurjP]
  refine ⟨m, ?_⟩
  apply Subtype.ext
  change (S3128Nf (G := G) f) ^ m * (a : A) =
    (S3128Nf (G := G) f) ^ m * (b : A)
  rw [hNpow]
  calc
    (f ^ m * P) * (a : A) = (f ^ m * (a : A)) * P := by ring
    _ = (f ^ m * (b : A)) * P := by rw [hc']
    _ = (f ^ m * P) * (b : A) := by ring

#check S3128ExistsOfEq

end LeanFormal.IUT.XiFPaper.S3128ExistsOfEqActual
end