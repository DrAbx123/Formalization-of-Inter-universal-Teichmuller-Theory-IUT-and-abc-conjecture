import Mathlib
open Module Matrix
noncomputable section
namespace ProbeBasisDet
variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (f : E →ₗ[ℚ_[p]] E) (bM bN : Basis n ℚ_[p] E)
variable (a : n → ℤ_[p]) (D : Matrix n n ℤ_[p])
theorem det_eq_unit_mul_prod
    (hrel : ∀ i, bN i = (a i : ℚ_[p]) • bM i)
    (hf : ∀ i, f (bM i) = ∑ j, (D j i : ℚ_[p]) • bN j)
    (hD : IsUnit D.det) :
    ∃ u : ℤ_[p]ˣ, LinearMap.det f = (u : ℚ_[p]) * ((∏ i, a i : ℤ_[p]) : ℚ_[p]) := by
  let uU := hD.unit
  refine ⟨uU, ?_⟩
  have hmat : LinearMap.toMatrix bM bM f =
      Matrix.diagonal (fun i => (a i : ℚ_[p])) * D.map (algebraMap ℤ_[p] ℚ_[p]) := by
    ext j i
    rw [LinearMap.toMatrix_apply, hf i]
    rw [Finset.sum_congr rfl (fun x hx => by
      by_cases hxj : x = j
      · subst x; simp [Matrix.diagonal_apply]
      · simp [hxj, Matrix.diagonal_apply, Finsupp.single_eq_of_ne hxj])] 
  rw [← LinearMap.det_toMatrix bM f, hmat, Matrix.det_mul, Matrix.det_diagonal]
  have hDmap : (D.map (algebraMap ℤ_[p] ℚ_[p])).det =
      ((D.det : ℤ_[p]) : ℚ_[p]) := by
    change ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix D).det = _
    rw [← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) D]
    rfl
  rw [hDmap]
  have hDval : (hD.unit : ℤ_[p]) = D.det := IsUnit.unit_spec hD
  rw [← hDval]
  push_cast
  ring
end ProbeBasisDet
