import tmp.sheaf.xif.paper.S3128BasicOpenQuotientActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128BasicOpenLocalizationUnitActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G] [Fintype G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]

/-- The image of N_f in B^G is a unit, assuming B = A_f and the fixed
subring algebra is the restricted fixed-subring map. -/
theorem S3128NfInv_image_isUnit
    {f : A} [Algebra A B] [IsLocalization.Away f B]
    [Algebra (S3128FixedSubring G A) (S3128FixedSubring G B)]
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    (hcomp : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B)
        (algebraMap A B) (fun g a => (halg g a).symm)) :
    IsUnit (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
      (S3128NfInv (G := G) (A := A) f)) := by
  have hN : IsUnit (algebraMap A B (S3128Nf (G := G) f)) :=
    S3128Nf_image_isUnit (G := G) (A := A) (B := B) (f := f) halg
  have hNinv : forall g : G,
      g • algebraMap A B (S3128Nf (G := G) f) =
        algebraMap A B (S3128Nf (G := G) f) := by
    intro g
    rw [halg, S3128Nf_invariant]
  obtain ⟨u, hu⟩ := hN.exists_left_inv
  have hu_inv : forall g : G, g • u = u := by
    intro g
    apply IsUnit.mul_right_cancel hN
    calc
      (g • u) * algebraMap A B (S3128Nf (G := G) f)
          = g • (u * algebraMap A B (S3128Nf (G := G) f)) := by
            rw [smul_mul', hNinv]
      _ = g • (1 : B) := by rw [hu]
      _ = (1 : B) := smul_one g
      _ = u * algebraMap A B (S3128Nf (G := G) f) := by rw [hu]
  have hu_unit : IsUnit u := IsUnit.of_mul_eq_one
    (algebraMap A B (S3128Nf (G := G) f)) hu
  let u_inv : B := ↑hu_unit.unit⁻¹
  have hu_left : u_inv * u = 1 := by
    simpa [u_inv, hu_unit.unit_spec] using Units.inv_mul hu_unit.unit
  have hu_inv_inv : forall g : G, g • u_inv = u_inv := by
    intro g
    apply IsUnit.mul_right_cancel hu_unit
    calc
      (g • u_inv) * u = g • (u_inv * u) := by rw [smul_mul', hu_inv]
      _ = g • (1 : B) := by rw [hu_left]
      _ = (1 : B) := smul_one g
      _ = u_inv * u := by rw [hu_left]
  let vUnit : (S3128FixedSubring G B)ˣ :=
    { val := ⟨u, hu_inv⟩
      inv := ⟨u_inv, hu_inv_inv⟩
      val_inv := by ext; simp [u_inv]
      inv_val := by ext; simp [u_inv] }
  have hsub : (S3128FixedSubring G B).subtype
      (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
        (S3128NfInv (G := G) (A := A) f)) =
        algebraMap A B (S3128Nf (G := G) f) := by
    rw [hcomp]
    simp [S3128FixedSubringMap, S3128NfInv, S3128Nf]
  have hprod : algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
        (S3128NfInv (G := G) (A := A) f) * (vUnit : S3128FixedSubring G B) = 1 := by
    apply Subtype.ext
    change (S3128FixedSubring G B).subtype
        (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
          (S3128NfInv (G := G) (A := A) f) *
            (vUnit : S3128FixedSubring G B)) = 1
    rw [map_mul, hsub]
    change algebraMap A B (S3128Nf (G := G) f) * u = 1
    rw [mul_comm]
    exact hu
  exact ⟨vUnit⁻¹, (Units.eq_inv_of_mul_eq_one_right hprod).symm⟩

#check S3128NfInv_image_isUnit

end LeanFormal.IUT.XiFPaper.S3128BasicOpenLocalizationUnitActual
end