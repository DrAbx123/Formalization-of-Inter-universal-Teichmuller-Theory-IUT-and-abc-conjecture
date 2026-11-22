import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open MvPolynomial
open scoped DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000

noncomputable section

namespace S1925Probe

variable {R : Type} [CommRing R]

/-- The defining homogeneous ideal of the projective closure. -/
abbrev relIdeal (F : MvPolynomial (Fin 3) R) : Ideal (MvPolynomial (Fin 3) R) := Ideal.span {F}

lemma relIdeal_isHomogeneous (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    (relIdeal F).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) R) := by
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨3, by rw [MvPolynomial.mem_homogeneousSubmodule]; exact hF⟩

/-- The homogeneous coordinate ring. -/
abbrev Cohom (F : MvPolynomial (Fin 3) R) : Type := MvPolynomial (Fin 3) R ⧸ relIdeal F

/-- The quotient map as an algebra map. -/
abbrev quo (F : MvPolynomial (Fin 3) R) : MvPolynomial (Fin 3) R →ₐ[R] Cohom F :=
  Ideal.Quotient.mkₐ R (relIdeal F)

/-- The grading of the homogeneous coordinate ring. -/
def CohomGr (F : MvPolynomial (Fin 3) R) (n : ℕ) : Submodule R (Cohom F) :=
  (MvPolynomial.homogeneousSubmodule (Fin 3) R n).map (quo (R := R) F).toLinearMap

lemma CohomGr_mem (F : MvPolynomial (Fin 3) R) {n : ℕ} {p : MvPolynomial (Fin 3) R}
    (hp : p.IsHomogeneous n) : quo F p ∈ CohomGr F n :=
  ⟨p, (MvPolynomial.mem_homogeneousSubmodule n p).mpr hp, rfl⟩

/-- The pointwise decomposition of a polynomial, transported to the quotient. -/
def decP (F : MvPolynomial (Fin 3) R) (p : MvPolynomial (Fin 3) R) :
    ⨁ n, CohomGr (R := R) F n :=
  DirectSum.mk (fun n => CohomGr (R := R) F n) (Finset.range (p.totalDegree + 1))
    (fun m => ⟨quo F (MvPolynomial.homogeneousComponent m.1 p),
      CohomGr_mem F (MvPolynomial.homogeneousComponent_isHomogeneous m.1 p)⟩)

lemma decP_apply (F : MvPolynomial (Fin 3) R) (p : MvPolynomial (Fin 3) R) (n : ℕ) :
    (decP F p n : Cohom F) = quo F (MvPolynomial.homogeneousComponent n p) := by
  rw [decP]
  by_cases hn : n < p.totalDegree + 1
  · rw [DirectSum.mk_apply_of_mem (Finset.mem_range.mpr hn)]
  · rw [DirectSum.mk_apply_of_notMem (by simpa using hn), Submodule.coe_zero]
    have hzero : MvPolynomial.homogeneousComponent n p = 0 := by
      apply MvPolynomial.homogeneousComponent_eq_zero
      omega
    rw [hzero, map_zero]

lemma decP_congr (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    {p q : MvPolynomial (Fin 3) R} (h : p - q ∈ relIdeal F) :
    decP F p = decP F q := by
  refine DFinsupp.ext fun n => Subtype.ext ?_
  rw [decP_apply, decP_apply]
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact MvPolynomial.homogeneousComponent_mem_of_mem (relIdeal_isHomogeneous F hF) h n

/-- The decomposition map on the quotient. -/
def decA (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) (x : Cohom F) :
    ⨁ n, CohomGr (R := R) F n :=
  Quotient.liftOn' x (decP F)
    (fun a b h => decP_congr F hF (by rwa [Submodule.quotientRel_def] at h))

lemma decA_mk (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    (p : MvPolynomial (Fin 3) R) :
    decA F hF (quo F p) = decP F p := by
  rw [decA, Ideal.Quotient.mkₐ_eq_mk]
  exact Quotient.liftOn'_mk p (decP F) _

end S1925Probe