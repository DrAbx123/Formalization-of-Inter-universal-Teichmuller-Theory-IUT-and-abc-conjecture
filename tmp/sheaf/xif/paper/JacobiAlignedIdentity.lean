import tmp.sheaf.xif.paper.TateJacobiHahnAttempt

noncomputable section

open LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt

namespace LeanFormal.IUT.XiFPaper.JacobiAlignedIdentity

variable {K : Type u} [Field K]

theorem alignedFactor (z : K) (m : Nat) :
    ((1 : HahnSeries Int K) - formalR ^ (4 * (m + 1))) *
      ((1 : HahnSeries Int K) +
        HahnSeries.single (4 * (m + 1) - 2 : Int) z) *
      ((1 : HahnSeries Int K) +
        HahnSeries.single (4 * (m + 1) - 2 : Int) z⁻¹) =
    ((1 : HahnSeries Int K) +
        (HahnSeries.C z * formalR ^ 2) * formalR ^ (4 * m)) *
      ((1 : HahnSeries Int K) +
        (HahnSeries.C z⁻¹ * formalR ^ 2) * formalR ^ (4 * m)) *
      ((1 : HahnSeries Int K) - formalR ^ (4 * (m + 1))) := by
  have hz : (HahnSeries.C z * formalR ^ 2) * formalR ^ (4 * m) =
      HahnSeries.single (4 * (m + 1) - 2 : Int) z := by
    simp [HahnSeries.C, formalR, HahnSeries.single_mul_single,
      HahnSeries.single_pow]
    ring_nf
  have hzi : (HahnSeries.C z⁻¹ * formalR ^ 2) * formalR ^ (4 * m) =
      HahnSeries.single (4 * (m + 1) - 2 : Int) z⁻¹ := by
    simp [HahnSeries.C, formalR, HahnSeries.single_mul_single,
      HahnSeries.single_pow]
    ring_nf
  rw [hz, hzi]
  ring

theorem S3134_jacobiAlignedProduct_identity (z : K) (N : Nat) :
    jacobiFormalProduct z N = jacobiAlignedProduct z N := by
  induction N with
  | zero => simp [jacobiFormalProduct, jacobiAlignedProduct]
  | succ N ih =>
      rw [jacobiFormalProduct, Finset.prod_range_succ]
      rw [← jacobiFormalProduct]
      rw [ih]
      conv_rhs => rw [jacobiAlignedProduct]
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ]
      have hsingle : HahnSeries.single (4 * (N + 1) : Int) (1 : K) =
          formalR ^ (4 * (N + 1)) := by
        simp [formalR, HahnSeries.single_pow]
      rw [hsingle]
      rw [jacobiAlignedProduct]
      rw [alignedFactor z N]
      ring

end LeanFormal.IUT.XiFPaper.JacobiAlignedIdentity
