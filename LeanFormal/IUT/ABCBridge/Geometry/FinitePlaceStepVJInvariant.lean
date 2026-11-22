import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.Foundations.LocalFields.LocalRootNormRepresentative

/-!
# Step (v) with the theta-pilot order read off from the `j`-invariant

IUT IV Theorem 1.10 Step (v) (`IV.txt` L1640–L1648) takes
`λ = ord(q̲_{v_j}^{j²})` with `q̲ = q_v^{1/2l}`.  The Step (v) container and its
volume depend only on `ord ϖ` (`FinitePlaceStepVAssembly`), and at a place of
multiplicative reduction `|q_v| = |j_E|⁻¹`.  This file feeds the actual
value-group representative of `LocalRootNormRepresentative` (single-agent-critical-gap)
into the actual-tuple hull theorem: for the local image `J` of `j_E` with
`‖J‖ > 1` and `2l ∣ ord(J⁻¹)` (actual DVR order), there is `ϖ` with
`ord ϖ = j²·(-ord J)/(2l)`, and the holomorphic hull of the possible images
`φ(ϖ · O_hol)` satisfies the paper's Step (v) bound with that `λ`.

Boundary: the divisibility `2l ∣ ord(J⁻¹)` is a hypothesis (in IUT it comes from
the torsion field `K ⊇ F(E[2l])`); no genuine Tate parameter, uniformization, or
source Kummer containment is claimed.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
  [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
  [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- **Step (v) from the `j`-invariant (actual tuple block).**  If `J` in the slot
`i†` has `‖J‖ > 1` and `2l` divides the actual DVR order of `J⁻¹`, then for every
label `j` there is a nonzero `ϖ` with `ord ϖ = j²·(-ord J)/(2l)` such that the
holomorphic hull of the possible images `φ(ϖ · O_hol)` has
`μ_log ≤ (-j²·(-ord J)/(2l) + ∑ d_i + 1)·log p + ∑_{i ∈ I*} (3 + log e_i)`. -/
theorem arithmeticTuple_stepV_hull_le_paperBound_of_jInvariant [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (istar : ι)
    [IsDiscreteValuationRing
      (LocalFieldIntegralUnits.Integers (CommonPrimeCompletion (places istar (tuple istar))))]
    (jValue : CommonPrimeCompletion (places istar (tuple istar))) (large_norm : 1 < ‖jValue‖)
    (l label : ℕ) (hl : 0 < 2 * l)
    (order_divisible : 2 * l ∣
      (IsDiscreteValuationRing.addVal
        (LocalFieldIntegralUnits.Integers (CommonPrimeCompletion (places istar (tuple istar))))
        (LocalRootNormRepresentative.inverseJInteger jValue large_norm)).toNat)
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hΦne : Φ.Nonempty)
    (hΦ : ∀ φ ∈ Φ, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    ∃ varpi : CommonPrimeCompletion (places istar (tuple istar)), varpi ≠ 0 ∧
      LocalFieldLogarithm.localNormOrder p varpi =
        (label : ℝ) ^ 2 * (-LocalFieldLogarithm.localNormOrder p jValue) / (2 * l : ℕ) ∧
      arithmeticTupleNormalizedLogVolume places tuple μ
          (arithmeticTupleHolomorphicHull places tuple e
            (arithmeticTupleStepVPossibleImages places tuple istar varpi Φ)) ≤
        (-((label : ℝ) ^ 2 * (-LocalFieldLogarithm.localNormOrder p jValue) / (2 * l : ℕ)) +
            ∑ i, LocalFieldLogarithm.localNormOrder p
              (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
          ∑ i ∈ exceptional, (3 + Real.log
            (LocalFieldLogarithm.logShellRamificationExponent
              (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)) := by
  obtain ⟨varpi, hvarpi, hord⟩ :=
    LocalRootNormRepresentative.exists_stepV_j_normOrder_representative (p := p)
      jValue large_norm (2 * l) hl label order_divisible
  refine ⟨varpi, hvarpi, hord, ?_⟩
  have h := arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound places tuple μ e istar
    varpi hvarpi Φ hΦne hΦ exceptional small_outside
  rwa [hord] at h

end

end LeanFormal.IUT.NumberFieldFinitePlace
