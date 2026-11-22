import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmCongruenceEquiv
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionPacketLogShell

/-!
# Explicit arithmetic decomposition of the log-shell integer index

For a complete ultrametric normed field `K` over `ℚ_[p]` satisfying the
standing hypotheses of the local log-shell construction, this file proves
three things.

1. **Cardinal decomposition.** The existing surjection from the unit group
   modulo the `p*`-congruence subgroup onto the additive quotient
   `integralLogShell / Integers` has kernel canonically isomorphic to the
   torsion subgroup of `(Integers K)ˣ`. Consequently
   `#((Integers K)ˣ ⧸ logShellCongruenceUnits) =
      #(torsion (Integers K)ˣ) * logShellIntegerIndex`,
   and equivalently the index is the quotient of the congruence-quotient
   cardinal by the torsion cardinal. No Haar measure or residue-field
   structure is needed for this identity.

2. **Conditional `q^a` extraction.** If a future local-invariant
   computation identifies the congruence-quotient cardinal with
   `q ^ a * #(torsion (Integers K)ˣ)`, the same cardinal identity cancels
   the torsion factor and yields `logShellIntegerIndex = q ^ a`. The
   concrete identification of `q` with the residue-field cardinality and
   of `a` with a ramification/valuation exponent is not asserted here:
   the available `Integers K` API has a local-ring and valuation-ring
   structure, but no finite residue field, discrete valuation ring, or
   ramification-index interface. The precise missing statements are
   recorded in the accompanying report.

3. **Isometry invariance.** A norm-preserving ring equivalence
   `K ≃+* L` maps the integral log-shell onto the integral log-shell and
   the integer subgroup onto the integer subgroup, hence induces an
   additive equivalence of the integer quotients and preserves
   `logShellIntegerIndex`. This is instantiated for the actual
   `CommonPrimeCompletion` of a finite place.

The Haar-measure route is recorded as a consistency corollary: the
existing measure formula combined with the cardinal decomposition gives
the same index as a quotient of congruence-quotient and torsion
cardinals.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

/-- The kernel of the comparison map from the congruence quotient to the
log-shell integer quotient has the cardinality of the torsion unit group.
This is the exact cardinal form of `torsionIntegerQuotientKernelEquiv`. -/
theorem card_congruenceQuotientToLogShellIntegers_ker :
    Nat.card (congruenceQuotientToLogShellIntegers (K := K) (p := p)).ker =
      Nat.card (CommGroup.torsion (Integers K)ˣ) :=
  Nat.card_congr (torsionIntegerQuotientKernelEquiv (K := K) (p := p)).toEquiv.symm

/-- First isomorphism theorem for the comparison map: the congruence
quotient has cardinality the kernel cardinality times the log-shell
integer quotient cardinality. -/
theorem card_logShellCongruenceQuotient_eq_ker_mul_index :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      Nat.card (congruenceQuotientToLogShellIntegers (K := K) (p := p)).ker *
        Nat.card (LogShellIntegerQuotient (K := K) (p := p)) := by
  let quotientHom := congruenceQuotientToLogShellIntegers (K := K) (p := p)
  have hquotient :
      Nat.card (((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ⧸
          quotientHom.ker) =
        Nat.card (LogShellIntegerQuotient (K := K) (p := p)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective quotientHom
      congruenceQuotientToLogShellIntegers_surjective).toEquiv
  rw [quotientHom.ker.card_eq_card_quotient_mul_card_subgroup, hquotient, Nat.mul_comm]

/-- Exact cardinal decomposition of the log-shell integer index by the
congruence quotient and the torsion subgroup of the integral units.

The only assumptions are the standing local-field hypotheses
`NormedField`, `CharZero`, `CompleteSpace`, `IsUltrametricDist`,
`ProperSpace`, `Fact p.Prime`, and `NormedAlgebra ℚ_[p] K`. No Haar
measure, Borel structure, residue field cardinality, or ramification
index is used. -/
theorem logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      Nat.card (CommGroup.torsion (Integers K)ˣ) *
        logShellIntegerIndex (K := K) (p := p) := by
  rw [card_logShellCongruenceQuotient_eq_ker_mul_index (K := K) (p := p),
    card_congruenceQuotientToLogShellIntegers_ker (K := K) (p := p)]
  rfl

/-- Division form of the exact decomposition. This is the precise sense
in which the index is the congruence-quotient order divided by the
torsion-unit order. -/
theorem logShellIntegerIndex_eq_card_div_torsion :
    logShellIntegerIndex (K := K) (p := p) =
      Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) /
        Nat.card (CommGroup.torsion (Integers K)ˣ) := by
  have htorsion : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  exact Nat.eq_div_of_mul_eq_right htorsion.ne'
    (logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex
      (K := K) (p := p)).symm

/-- Conditional `q^a` extraction. If a local-invariant computation
identifies the congruence-quotient order with `q ^ a` times the torsion
order, the torsion factor cancels and the index is exactly `q ^ a`.
The identification of `q` with a residue-field cardinality and `a` with
a ramification exponent is deliberately not asserted here; see the
accompanying report for the missing local-invariant interfaces. -/
theorem logShellIntegerIndex_eq_pow_of_card_eq_pow_mul_torsion
    {q a : ℕ}
    (hcard : Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      q ^ a * Nat.card (CommGroup.torsion (Integers K)ˣ)) :
    logShellIntegerIndex (K := K) (p := p) = q ^ a := by
  have htorsion : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  have hmul :
      q ^ a * Nat.card (CommGroup.torsion (Integers K)ˣ) =
        logShellIntegerIndex (K := K) (p := p) *
          Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    rw [← hcard,
      logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex (K := K) (p := p),
      Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_right htorsion hmul.symm

section HaarConsistency

open MeasureTheory

variable [MeasurableSpace K] [BorelSpace K]

/-- Haar-measure consistency of the cardinal decomposition: the measure
of the integral log-shell is the congruence-quotient order divided by the
torsion order, times the measure of the integer ring. -/
theorem measure_integralLogShell_eq_card_div_torsion_mul
    (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := K) (p := p) : Set K) =
      ((Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) /
        Nat.card (CommGroup.torsion (Integers K)ˣ) : ℕ) : ENNReal) *
        μ (Integers K : Set K) := by
  rw [measure_integralLogShell_eq_index_mul (K := K) (p := p) μ,
    logShellIntegerIndex_eq_card_div_torsion (K := K) (p := p)]

end HaarConsistency

section IsometryInvariance

variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
variable [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]
  [CharZero L] [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L] in
/-- The inverse of a norm-preserving ring equivalence is an isometry. -/
theorem integralLogShell_isometry_ringEquiv_symm (e : K ≃+* L)
    (he : Isometry (e : K → L)) : Isometry (e.symm : L → K) := by
  refine Isometry.of_dist_eq ?_
  intro x y
  rw [← he.dist_eq (e.symm x) (e.symm y), e.apply_symm_apply, e.apply_symm_apply]

omit [CharZero K] [CompleteSpace K] [ProperSpace K]
  [CharZero L] [CompleteSpace L] [ProperSpace L] in
/-- A norm-preserving ring equivalence preserves membership in the
integer ring. -/
theorem integralLogShell_isometry_mem_integers_iff (e : K ≃+* L)
    (he : Isometry (e : K → L)) (x : K) :
    e x ∈ Integers L ↔ x ∈ Integers K := by
  rw [mem_integers_iff, mem_integers_iff]
  have h : ‖e x‖ = ‖x‖ := norm_map_of_isometry (e : K →+* L) he x
  rw [h]

/-- Restriction of a norm-preserving ring equivalence to an additive
equivalence of integral log-shells. -/
def integralLogShellAddEquivOfRingEquiv (e : K ≃+* L)
    (he : Isometry (e : K → L)) :
    integralLogShell (K := K) (p := p) ≃+ integralLogShell (K := L) (p := p) where
  toFun x := ⟨e x, map_mem_integralLogShell (p := p) (e : K →+* L) he x.property⟩
  invFun y := ⟨e.symm y,
    map_mem_integralLogShell (p := p) (e.symm : L →+* K)
      (integralLogShell_isometry_ringEquiv_symm e he) y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

/-- The additive equivalence of shells maps the integer subgroup onto the
integer subgroup. -/
theorem integralLogShell_map_integerSubgroup_eq (e : K ≃+* L)
    (he : Isometry (e : K → L)) :
    AddSubgroup.map (integralLogShellAddEquivOfRingEquiv (p := p) e he)
      (logShellIntegerSubgroup (K := K) (p := p)) =
    logShellIntegerSubgroup (K := L) (p := p) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : K) ∈ Integers K :=
      (mem_logShellIntegerSubgroup_iff (K := K) (p := p) x).mp hx
    exact (mem_logShellIntegerSubgroup_iff (K := L) (p := p)
      (integralLogShellAddEquivOfRingEquiv e he x)).mpr
      (by
        change e (x : K) ∈ Integers L
        exact (integralLogShell_isometry_mem_integers_iff e he (x : K)).mpr hx')
  · intro hy
    have hy' : (y : L) ∈ Integers L :=
      (mem_logShellIntegerSubgroup_iff (K := L) (p := p) y).mp hy
    let x : integralLogShell (K := K) (p := p) :=
      ⟨e.symm (y : L),
        map_mem_integralLogShell (p := p) (e.symm : L →+* K)
          (integralLogShell_isometry_ringEquiv_symm e he) y.property⟩
    refine ⟨x, ?_, ?_⟩
    · exact (mem_logShellIntegerSubgroup_iff (K := K) (p := p) x).mpr
        ((integralLogShell_isometry_mem_integers_iff e he (e.symm (y : L))).mp (by
          simpa using hy'))
    · ext
      change e (e.symm (y : L)) = (y : L)
      simp

/-- Additive equivalence of the integer quotients induced by a
norm-preserving ring equivalence. -/
def logShellIntegerQuotientAddEquivOfRingEquiv (e : K ≃+* L)
    (he : Isometry (e : K → L)) :
    LogShellIntegerQuotient (K := K) (p := p) ≃+
      LogShellIntegerQuotient (K := L) (p := p) :=
  QuotientAddGroup.congr
    (logShellIntegerSubgroup (K := K) (p := p))
    (logShellIntegerSubgroup (K := L) (p := p))
    (integralLogShellAddEquivOfRingEquiv (p := p) e he)
    (integralLogShell_map_integerSubgroup_eq (p := p) e he)

/-- The log-shell integer index is invariant under norm-preserving ring
equivalences of the ambient local field. -/
theorem logShellIntegerIndex_eq_of_isometry_ringEquiv (e : K ≃+* L)
    (he : Isometry (e : K → L)) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellIntegerIndex (K := L) (p := p) :=
  Nat.card_congr
    (logShellIntegerQuotientAddEquivOfRingEquiv (p := p) e he).toEquiv

end IsometryInvariance

section CommonPrimeCompletion

open LeanFormal.IUT.NumberFieldFinitePlace

local instance normalizedCompletionNormedAlgebraAtPrime
    {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (place : FinitePlaceAtPrime F p) :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) :=
  commonPrimeCompletionNormedAlgebra (p := p) place

/-- The actual common prime completion has the same log-shell integer
index as the normalized completion defining it. -/
theorem logShellIntegerIndex_commonPrimeCompletion_eq_normalizedCompletion
    {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (place : FinitePlaceAtPrime F p) :
    logShellIntegerIndex (K := CommonPrimeCompletion place) (p := p) =
      logShellIntegerIndex (K := NormalizedCompletion place.val) (p := p) :=
  logShellIntegerIndex_eq_of_isometry_ringEquiv (p := p)
    (commonPrimeCompletionRingEquiv place)
    (isometry_commonPrimeCompletionRingEquiv place)

/-- The exact cardinal decomposition instantiated at the actual common
prime completion. -/
theorem card_logShellCongruenceQuotient_commonPrimeCompletion
    {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (place : FinitePlaceAtPrime F p) :
    Nat.card ((Integers (CommonPrimeCompletion place))ˣ ⧸
        logShellCongruenceUnits (K := CommonPrimeCompletion place) (p := p)) =
      Nat.card (CommGroup.torsion (Integers (CommonPrimeCompletion place))ˣ) *
        logShellIntegerIndex (K := CommonPrimeCompletion place) (p := p) :=
  logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex
    (K := CommonPrimeCompletion place) (p := p)

end CommonPrimeCompletion

end

end LeanFormal.IUT.LocalFieldLogarithm
