import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellScalarClosure

/-!
# task-68: integral-log-shell self-similarity under p-adic UNIT scalars (F4 b2 core)

**COMPONENT, not a paper object.**  Consumer: F4 (b2) `S3135LogShellUnitSelfSimilarity`.

The actual `integralLogShell` is defined as the image of the scaled unit logarithm
(`IntegralUnitLogarithm.lean:194`), so it is an additive subgroup closed under
multiplication by p-adic integral scalars
(`integralLogShell_padicInt_mul_mem`, `IntegralLogShellScalarClosure.lean:14`).
For a p-adic UNIT scalar (norm 1, the paper's `|lambda| = 1`,
i.e. log-degree 0 / procession normalization) both `z` and `z⁻¹` are integral, so
multiplication by `z` preserves the actual log-shell:

`(fun x => algebraMap Q_p K (z : Q_p) * x) '' integralLogShell = integralLogShell`.

Combined with the landed reduction `s3135_haar_normalized_of_unitScaling`
(which forces the Haar modulus to 1 once the unit compact is invariant) and the
preimage-mass/scalar-factor results (`S3135HaarUniquenessToolActual`,
`S3135ScalarFactorMassActual`), this gives `mu(lambda·O) = mu(O)` for the paper
scaling when the paper `lambda` is realized as the base-field p-adic unit scalar
(the procession-normalization datum; IUT III Proposition 3.9(i) p.115;
Remark 3.9.5(i) pp.158-159).  The identification of the paper `lambda` with such a
base-field unit scalar is a named model datum, kept explicit.
-/

noncomputable section

open LeanFormal.IUT.LocalFieldLogarithm

namespace LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- **Integral-log-shell self-similarity under a p-adic unit scalar**: if
`z * z' = 1` in `Z_[p]`, then multiplication by the scalar `z` preserves the
actual integral log-shell. -/
theorem s3135_integralLogShell_scalarUnit_selfSimilarity
    (z z' : ℤ_[p]) (h : z * z' = 1) :
    (fun x : K => algebraMap ℚ_[p] K (z : ℚ_[p]) * x) ''
        ((integralLogShell (K := K) (p := p)) : Set K) =
      ((integralLogShell (K := K) (p := p)) : Set K) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact integralLogShell_padicInt_mul_mem z hx
  · intro hy
    refine ⟨algebraMap ℚ_[p] K (z' : ℚ_[p]) * y,
      integralLogShell_padicInt_mul_mem z' hy, ?_⟩
    change algebraMap ℚ_[p] K (z : ℚ_[p]) *
      (algebraMap ℚ_[p] K (z' : ℚ_[p]) * y) = y
    rw [← mul_assoc, ← map_mul]
    have hcast : (z : ℚ_[p]) * (z' : ℚ_[p]) = 1 := by
      have hz : (z * z' : ℤ_[p]) = 1 := h
      have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hz
      simpa using this
    rw [hcast, map_one, one_mul]

#check s3135_integralLogShell_scalarUnit_selfSimilarity

end LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual
end
