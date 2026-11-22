import tmp.sheaf.xif.paper.S2531Mod1249FactorActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual

noncomputable section
open Polynomial
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2671Mod1249FactorDegreesActual

open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2531Mod1249FactorActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

structure S2671FactorizationData (R : Type*) [CommRing R] (g : R[X]) where
  c : R
  c_ne_zero : c ≠ 0
  g2 : R[X]
  g10 : R[X]
  product_eq : g = C c * (g2 * g10)
  g2_monic : g2.Monic
  g10_monic : g10.Monic
  g2_irreducible : Irreducible g2
  g10_irreducible : Irreducible g10
  g2_degree : g2.natDegree = 2
  g10_degree : g10.natDegree = 10

theorem S2671_factorDegrees_of_factors
    {R : Type} [Field R] (c : R) (hc : c ≠ 0)
    (g2 g10 : R[X])
    (h2m : g2.Monic) (h10m : g10.Monic)
    (h2i : Irreducible g2) (h10i : Irreducible g10)
    (h2deg : g2.natDegree = 2) (h10deg : g10.natDegree = 10) :
    factorDegrees (C c * (g2 * g10)) = ({2, 10} : Multiset ℕ) := by
  classical
  have hcC : (C c : R[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have hg2 : g2 ≠ 0 := h2m.ne_zero
  have hg10 : g10 ≠ 0 := h10m.ne_zero
  have hprod : g2 * g10 ≠ 0 := mul_ne_zero hg2 hg10
  have hnf : UniqueFactorizationMonoid.normalizedFactors (C c * (g2 * g10)) =
      ({g2, g10} : Multiset R[X]) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hcC hprod,
      UniqueFactorizationMonoid.normalizedFactors_of_isUnit
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)),
      Multiset.zero_add,
      UniqueFactorizationMonoid.normalizedFactors_mul hg2 hg10,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h2i,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h10i,
      Monic.normalize_eq_self h2m, Monic.normalize_eq_self h10m]
    simp
  rw [show factorDegrees (C c * (g2 * g10)) =
      (UniqueFactorizationMonoid.normalizedFactors (C c * (g2 * g10))).map
        Polynomial.natDegree from rfl]
  rw [hnf]
  simp [h2deg, h10deg]

theorem S2671F2_monic : S2550F2.Monic := by
  unfold S2550F2
  monicity!

theorem S2671F10_monic : S2550F10.Monic := by
  unfold S2550F10
  monicity!

theorem S2671F2_irreducible : Irreducible S2550F2 := by
  have h415 : IsUnit (C (415 : ZMod 1249)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by decide))
  have hassoc : Associated (C (415 : ZMod 1249) * S2550F2) S2550F2 :=
    associated_unit_mul_left S2550F2 (C (415 : ZMod 1249)) h415
  exact (hassoc.irreducible g2_irreducible)

theorem S2671F10_irreducible : Irreducible S2550F10 := g10_irreducible

theorem S2671F2_degree : S2550F2.natDegree = 2 := by
  unfold S2550F2
  compute_degree!

theorem S2671F10_degree : S2550F10.natDegree = 10 := by
  unfold S2550F10
  compute_degree!

noncomputable def S2671Mod1249FactorizationData : Prop :=
  True

theorem S2671FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 1249))) =
      ({2, 10} : Multiset ℕ) := by
  rw [← S2550Psi5Mod1249_eq, S2550Product]
  exact S2671_factorDegrees_of_factors (415 : ZMod 1249) (by decide)
    S2550F2 S2550F10 S2671F2_monic S2671F10_monic
    S2671F2_irreducible S2671F10_irreducible S2671F2_degree S2671F10_degree

#check S2671FactorDegrees
#print axioms S2671FactorDegrees

end LeanFormal.IUT.XiFPaper.S2671Mod1249FactorDegreesActual
end
