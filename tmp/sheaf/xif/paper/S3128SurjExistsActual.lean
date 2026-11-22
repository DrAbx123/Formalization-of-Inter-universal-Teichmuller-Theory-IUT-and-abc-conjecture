import tmp.sheaf.xif.paper.S3128SurjAverageImageActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjExistsActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128AverageActual
open LeanFormal.IUT.XiFPaper.S3128SurjHtermActual
open LeanFormal.IUT.XiFPaper.S3128SurjAverageImageActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B] [Algebra A B]
  [Algebra (S3128FixedSubring G A) (S3128FixedSubring G B)]

/-- Surjectivity witness: s * NInv^n is in the image of A^G. -/
theorem S3128Surj_exists_a
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm))
    (hcard : IsUnit (Fintype.card G : A))
    (f a0 : A) (n : Nat) (s : S3128FixedSubring G B)
    (hm : (s : B) * algebraMap A B (f ^ n) = algebraMap A B a0) :
    ∃ a : S3128FixedSubring G A,
      (s : S3128FixedSubring G B) *
          (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
            (S3128NfInv (G := G) (A := A) f)) ^ n =
        algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) a := by
  let b : A := S3128SurjB G A a0 f n
  let c : A := S3128Average (G := G) (A := A) hcard b
  let inv : c ∈ S3128FixedSubring G A :=
    fun k => S3128Average_invariant (G := G) (A := A) hcard b k
  refine ⟨⟨c, inv⟩, ?_⟩
  have hsub : (S3128FixedSubring G B).subtype
      (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
        (S3128NfInv (G := G) (A := A) f)) =
        algebraMap A B (S3128Nf (G := G) f) := by
    rw [hcomp]
    simp [S3128FixedSubringMap, S3128NfInv, S3128Nf]
  apply Subtype.ext
  change (S3128FixedSubring G B).subtype
      ((s : S3128FixedSubring G B) *
        (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
          (S3128NfInv (G := G) (A := A) f)) ^ n) =
    (S3128FixedSubring G B).subtype
      (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) ⟨c, inv⟩)
  rw [map_mul, map_pow, hsub, hcomp]
  simp [S3128FixedSubringMap]
  exact (S3128Surj_average_image (G := G) (A := A) (B := B)
    hcard halg f a0 n s hm).symm


/-- Surjectivity of A^G → B^G at NInv. -/
theorem S3128Surj_actual
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm))
    (hcard : IsUnit (Fintype.card G : A))
    (f : A) [IsLocalization.Away f B] :
    forall s : S3128FixedSubring G B,
      exists (n : Nat) (a : S3128FixedSubring G A),
        (s : S3128FixedSubring G B) *
            (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
              (S3128NfInv (G := G) (A := A) f)) ^ n =
          algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) a := by
  intro s
  obtain ⟨⟨a0, m⟩, hm⟩ :=
    IsLocalization.surj (Submonoid.powers f) (s : B)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m.val f).mp m.property
  have hm' : (s : B) * algebraMap A B (f ^ n) = algebraMap A B a0 := by
    simpa [← hn] using hm
  exact ⟨n, S3128Surj_exists_a (G := G) (A := A) (B := B)
    halg hcomp hcard f a0 n s hm'⟩

#check S3128Surj_actual

#check S3128Surj_exists_a

end LeanFormal.IUT.XiFPaper.S3128SurjExistsActual
end