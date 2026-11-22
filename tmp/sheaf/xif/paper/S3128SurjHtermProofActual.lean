import tmp.sheaf.xif.paper.S3128SurjHtermActual
import tmp.sheaf.xif.paper.S3128SurjProductActual
import tmp.sheaf.xif.paper.S3128BasicOpenQuotientActual
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjHtermProofActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SurjHtermActual
open LeanFormal.IUT.XiFPaper.S3128SurjProductActual
open LeanFormal.IUT.XiFPaper.S3128SurjHa0Actual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B] [Algebra A B]

/-- The algebraMap image of h • b is s * N^n. -/
theorem S3128Surj_hterm
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (f a0 : A) (n : Nat) (s : S3128FixedSubring G B)
    (hm : (s : B) * algebraMap A B (f ^ n) = algebraMap A B a0)
    (h : G) :
    algebraMap A B (h • S3128SurjB G A a0 f n) =
      (s : B) * (algebraMap A B (S3128Nf (G := G) f)) ^ n := by
  rw [S3128Surj_hb, map_mul]
  rw [S3128Surj_ha0 halg hm (fun k => s.property k) h]
  rw [mul_assoc, ← map_mul, S3128Surj_prodN]
  rw [Finset.prod_pow]
  change (s : B) * algebraMap A B ((S3128Nf (G := G) f) ^ n) = _
  rw [map_pow]

#check S3128Surj_hterm

end LeanFormal.IUT.XiFPaper.S3128SurjHtermProofActual
end