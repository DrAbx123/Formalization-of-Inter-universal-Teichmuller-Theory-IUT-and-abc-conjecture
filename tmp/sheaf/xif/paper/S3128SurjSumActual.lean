import tmp.sheaf.xif.paper.S3128SurjHtermProofActual
import tmp.sheaf.xif.paper.S3128AverageActual
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjSumActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SurjHtermActual
open LeanFormal.IUT.XiFPaper.S3128SurjHtermProofActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B] [Algebra A B]

/-- The algebraMap image of the sum of h • b. -/
theorem S3128Surj_sum_image
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (f a0 : A) (n : Nat) (s : S3128FixedSubring G B)
    (hm : (s : B) * algebraMap A B (f ^ n) = algebraMap A B a0) :
    algebraMap A B (∑ h : G, h • S3128SurjB G A a0 f n) =
      (Fintype.card G : B) * (s * (algebraMap A B (S3128Nf (G := G) f)) ^ n) := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun h _ =>
    S3128Surj_hterm halg f a0 n s hm h)]
  rw [Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_mul]

#check S3128Surj_sum_image

end LeanFormal.IUT.XiFPaper.S3128SurjSumActual
end