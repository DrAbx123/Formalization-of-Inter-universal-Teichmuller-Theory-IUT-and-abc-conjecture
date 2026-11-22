import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificate
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-!
# N8 group 6: repository-internal normalization conversion

This file proves only a finite identity between two normalizations already
present in the repository:

- the signed raw Haar log
  arithmeticTupleCanonicalHullHaarLog, i.e.
  L_mu(S) = log((mu S).toReal);
- the degree-normalized local log-volume
  arithmeticTupleNormalizedLogVolume, i.e.
  V_mu(S) = (L_mu(S) - L_mu(canonicalUnitReference)) / D,
  with D = finrank_{Q_p} the degree of the local tensor block.

The main theorem is the exact conversion

L_mu(H) = D * V_mu(H) + L_mu(canonicalUnitReference).

The specialization mu canonicalUnitReference = 1 is the corollary in which the
additive constant vanishes. This is a repository-internal normalization
calculation. It does NOT identify either side with the paper's -|log(Theta)|,
does NOT construct the paper's normalized/procession log volume, and does NOT
connect the normalization to (Ob3-3), to source comparisons, or to the global
all-places degree.

## Not connected here

- arithmeticTupleNormalizedLogVolume_primeScalar_zpow calibrates a p-scalar
  power in the degree-normalized local log-volume; this file does not transport
  that calibration to the signed certificate.
- Label averaging, local weights, and the determinant tensor M are not
  connected here.
- The +inf/unbounded branch of the extended log-volume is a separate
  obligation and is not handled by this finite identity.
- No production file is edited; this file is not imported by Project.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory

universe u v w

/-- Exact conversion between the raw signed Haar log of the canonical hull and
the degree-normalized local log-volume. This is the general formula with the
additive reference-log term retained; no unit-reference normalization is
assumed. -/
theorem n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume_add_log_unitReference
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] :
    arithmeticTupleCanonicalHullHaarLog places tuple mu =
      (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
          arithmeticTupleNormalizedLogVolume places tuple mu
            (arithmeticTupleCanonicalHull places tuple) +
        Real.log
          (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
  have hD : (Module.finrank ℚ_[p]
      (ArithmeticTensorTupleBlock places tuple) : Real) ≠ 0 := by
    exact_mod_cast (finrank_arithmeticTensorTupleBlock_pos places tuple).ne'
  simp only [arithmeticTupleCanonicalHullHaarLog,
    arithmeticTupleNormalizedLogVolume]
  field_simp [hD]
  ring

/-- Corollary under the additive-Haar normalization
mu canonicalUnitReference = 1: the raw signed Haar log is exactly D times
the degree-normalized local log-volume. -/
theorem n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume_of_unitReference_measure_one
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu]
    (hunit : mu (arithmeticTupleCanonicalUnitReference places tuple) = 1) :
    arithmeticTupleCanonicalHullHaarLog places tuple mu =
      (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
        arithmeticTupleNormalizedLogVolume places tuple mu
          (arithmeticTupleCanonicalHull places tuple) := by
  rw [n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume_add_log_unitReference
    places tuple mu, hunit, ENNReal.toReal_one, Real.log_one, add_zero]

end LeanFormal.IUT.NumberFieldFinitePlace
