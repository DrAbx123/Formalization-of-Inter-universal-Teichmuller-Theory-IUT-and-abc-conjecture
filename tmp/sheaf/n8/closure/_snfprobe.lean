import Mathlib
open Matrix
namespace ProbeSNF
variable {p : Nat} [Fact p.Prime]
theorem det_snf_eq_unit_mul_prod {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℤ_[p]) (a : n → ℤ_[p])
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    ∃ u : ℤ_[p]ˣ, (U * Matrix.diagonal a * V).det = (u : ℤ_[p]) * ∏ i, a i := by
  let uU := hU.unit
  let uV := hV.unit
  refine ⟨uU * uV, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hUval : (uU : ℤ_[p]) = U.det := IsUnit.unit_spec hU
  have hVval : (uV : ℤ_[p]) = V.det := IsUnit.unit_spec hV
  rw [← hUval, ← hVval]
  simp [Units.val_mul, mul_assoc, mul_left_comm, mul_comm]
end ProbeSNF
