import tmp.sheaf.xif.paper.S3128SurjSumActual

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjAverageImageActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128AverageActual
open LeanFormal.IUT.XiFPaper.S3128SurjHtermActual
open LeanFormal.IUT.XiFPaper.S3128SurjSumActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B] [Algebra A B]

/-- AlgebraMap image of the averaged b is s * N^n. -/
theorem S3128Surj_average_image
    (hcard : IsUnit (Fintype.card G : A))
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (f a0 : A) (n : Nat) (s : S3128FixedSubring G B)
    (hm : (s : B) * algebraMap A B (f ^ n) = algebraMap A B a0) :
    algebraMap A B (S3128Average (G := G) (A := A) hcard
        (S3128SurjB G A a0 f n)) =
      (s : B) * (algebraMap A B (S3128Nf (G := G) f)) ^ n := by
  let hcardB : IsUnit (algebraMap A B (Fintype.card G : A)) :=
    hcard.map (algebraMap A B)
  have hmap_inv : algebraMap A B (((hcard.unit⁻¹ : Aˣ) : A)) =
      ((hcardB.unit⁻¹ : Bˣ) : B) := by
    have hA : (((hcard.unit⁻¹ : Aˣ) : A)) * (Fintype.card G : A) = 1 := by
      simpa [hcard.unit_spec] using Units.inv_mul hcard.unit
    have hB : (((hcardB.unit⁻¹ : Bˣ) : B)) *
        algebraMap A B (Fintype.card G : A) = 1 := by
      simpa [hcardB.unit_spec] using Units.inv_mul hcardB.unit
    apply IsUnit.mul_right_cancel hcardB
    calc
      algebraMap A B (((hcard.unit⁻¹ : Aˣ) : A)) *
          algebraMap A B (Fintype.card G : A)
          = algebraMap A B (1 : A) := by rw [← map_mul, hA, map_one]
      _ = ((hcardB.unit⁻¹ : Bˣ) : B) *
          algebraMap A B (Fintype.card G : A) := by
        rw [map_one, hB]
  unfold S3128Average
  rw [map_mul, hmap_inv, S3128Surj_sum_image halg f a0 n s hm]
  have hcard_coe : (Fintype.card G : B) =
      algebraMap A B (Fintype.card G : A) := by simp
  rw [hcard_coe]
  have hcancel : (((hcardB.unit⁻¹ : Bˣ) : B)) *
      algebraMap A B (Fintype.card G : A) = 1 := by
    simpa [hcardB.unit_spec] using Units.inv_mul hcardB.unit
  rw [← mul_assoc, hcancel, one_mul]

#check S3128Surj_average_image

end LeanFormal.IUT.XiFPaper.S3128SurjAverageImageActual
end