import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Residue-field normalisation of the log-shell integer index

The arithmetic decomposition in `IntegralLogShellIndexArithmetic` expresses
the log-shell integer index as the congruence-quotient order divided by the
order of the torsion unit group. This file records the unconditional
residue-field part of the expected local `q/e/f` normalisation and isolates
the remaining cardinal computation in a single named hypothesis.

For a proper nonarchimedean normed field `K`, Mathlib proves that the
valuation ring has finite residue field. Hence the residue cardinal `q` is
finite and strictly larger than one. The still missing input is the exact
cardinality of the `p*`-congruence quotient in terms of `q`, the ramification
data, and the torsion-unit order. No such formula is assumed silently: the
reductions below take it as an explicit hypothesis and state the resulting
identity for `logShellIntegerIndex`.

The unconditional residue-field part is complete: `q` is the actual residue
cardinal, it is finite, positive, and strictly larger than one. The exact
`q/e/f` input that remains is recorded by `LogShellQFECardinalityHypothesis`:
the residue cardinal is `p ^ f`, and the `p*`-congruence quotient has order
`q ^ (e * s - 1) * (q - 1)`, where `e` is the ramification exponent and
`s = 2` at `p = 2`, `s = 1` otherwise. The missing Mathlib interface is a
discrete-valuation-ring and principal-congruence-filtration computation for
`Integers K`: an `IsDiscreteValuationRing (Integers K)` instance, the
identification of `logShellCongruenceUnits` with `1 + logShellScale p * O_K`,
and the quotient cardinality `#(O_K / (logShellScale p)) = q ^ (e * s)`.
The consumers are
`logShellIntegerIndex_eq_residueCard_pow_mul_sub_one_div_torsion_of_qfe`
and the Haar-measure discrepancy formula in `IntegralLogShellHaarIndex`.
The divisibility `#torsion ∣ q - 1` used to split off a pure `q`-power is a
separate named hypothesis; it is not automatic from the standing hypotheses.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]

/-- The residue field of the actual integer ring used by the log-shell. -/
abbrev logShellResidueField : Type _ :=
  IsLocalRing.ResidueField (Integers K)

/-- The cardinality `q` of the residue field of the actual integer ring. -/
def logShellResidueCard : Nat :=
  Nat.card (logShellResidueField (K := K))

include localNormedAlgebra

omit [CharZero K] [CompleteSpace K] in
/-- Properness of the nonarchimedean local field makes the residue field of
its actual integer ring finite. -/
theorem finite_logShellResidueField : Finite (logShellResidueField (K := K)) := by
  letI : CompactSpace (Integers K) :=
    isCompact_iff_compactSpace.mp (isCompact_valuationIntegerLattice (K := K) (p := p))
  have htb : TotallyBounded (Set.univ : Set (Integers K)) := isCompact_univ.totallyBounded
  obtain ⟨t, _ht, htfin, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded htb (1 / 2 : ℝ) (by norm_num)
  have hrange : Set.range (IsLocalRing.residue (Integers K)) ⊆
      (t.image (IsLocalRing.residue (Integers K)) : Set (logShellResidueField (K := K))) := by
    rintro z ⟨x, rfl⟩
    have hxcover := hcover (Set.mem_univ x)
    simp only [Set.mem_iUnion, exists_prop] at hxcover
    obtain ⟨y, hyt, hxy⟩ := hxcover
    refine ⟨y, hyt, ?_⟩
    change IsLocalRing.residue (Integers K) y = IsLocalRing.residue (Integers K) x
    rw [eq_comm]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    rintro ⟨u, hu⟩
    have hdist1 : dist x y < 1 :=
      (Metric.mem_ball.mp hxy).trans (by norm_num : (1 / 2 : ℝ) < 1)
    have hsubnorm : ‖((x - y : Integers K) : K)‖ < 1 := by
      rw [dist_eq_norm] at hdist1
      simpa using hdist1
    have hnorm := norm_unit_eq_one (K := K) u
    rw [hu] at hnorm
    exact (ne_of_lt hsubnorm) hnorm
  have hfin : (Set.range (IsLocalRing.residue (Integers K))).Finite :=
    (htfin.image (IsLocalRing.residue (Integers K))).subset hrange
  rw [← Set.finite_univ_iff]
  rw [← Set.range_eq_univ.mpr (IsLocalRing.residue_surjective (R := Integers K))]
  exact hfin

omit [CharZero K] [CompleteSpace K] in
/-- The residue cardinal of the actual integer ring is positive. -/
theorem logShellResidueCard_pos : 0 < logShellResidueCard (K := K) := by
  letI := finite_logShellResidueField (K := K) (p := p)
  exact Nat.card_pos

omit [CharZero K] [CompleteSpace K] in
/-- The residue field is nontrivial, so its cardinal is strictly larger than one. -/
theorem one_lt_logShellResidueCard : 1 < logShellResidueCard (K := K) := by
  letI := finite_logShellResidueField (K := K) (p := p)
  exact Finite.one_lt_card

/-- The exact remaining local cardinal input: the `p*`-congruence quotient has
order `q ^ a` times the torsion-unit order. Here `q` is fixed to be the actual
residue cardinal, while the exponent `a` records the missing ramification and
principal-filtration computation. -/
def LogShellResiduePowerCardHypothesis (a : Nat) : Prop :=
  Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
    logShellResidueCard (K := K) ^ a *
      Nat.card (CommGroup.torsion (Integers K)ˣ)

/-- Under the named residue-power cardinal hypothesis, the log-shell integer
index is exactly the power `q ^ a` of the actual residue cardinal. -/
theorem logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
    {a : Nat} (hcard : LogShellResiduePowerCardHypothesis (K := K) (p := p) a) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^ a :=
  logShellIntegerIndex_eq_pow_of_card_eq_pow_mul_torsion (K := K) (p := p) hcard

/-- The general named cardinal input with an explicit correction factor `c`.
The factor records exactly the discrepancy between the `p*`-congruence
quotient and the pure residue power after removing torsion units. -/
def LogShellResiduePowerCardCorrectionHypothesis (a c : Nat) : Prop :=
  Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
    logShellResidueCard (K := K) ^ a *
      Nat.card (CommGroup.torsion (Integers K)ˣ) * c

/-- The correction form of the reduction: the log-shell index is `q ^ a * c`.
The torsion-unit order cancels because it is a positive factor of the
already proved congruence-quotient decomposition. -/
theorem logShellIntegerIndex_eq_residueCard_pow_mul_correction_of_card
    {a c : Nat}
    (hcard : LogShellResiduePowerCardCorrectionHypothesis (K := K) (p := p) a c) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^ a * c := by
  have htorsion : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  have hdecomp :=
    logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex (K := K) (p := p)
  have hcancel :
      Nat.card (CommGroup.torsion (Integers K)ˣ) *
          logShellIntegerIndex (K := K) (p := p) =
        Nat.card (CommGroup.torsion (Integers K)ˣ) *
          (logShellResidueCard (K := K) ^ a * c) := by
    calc
      Nat.card (CommGroup.torsion (Integers K)ˣ) *
          logShellIntegerIndex (K := K) (p := p) =
          Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) :=
        hdecomp.symm
      _ = logShellResidueCard (K := K) ^ a *
          Nat.card (CommGroup.torsion (Integers K)ˣ) * c := hcard
      _ = Nat.card (CommGroup.torsion (Integers K)ˣ) *
          (logShellResidueCard (K := K) ^ a * c) := by ring
  exact Nat.eq_of_mul_eq_mul_left htorsion hcancel

/-- The factor `s` in `logShellScale p = p ^ s`: it is `2` at `p = 2`
and `1` at odd `p`. Hence `v_K(logShellScale p) = e * s` when `e` is the
ramification exponent `v_K(p)`. -/
def logShellScaleExponentFactor : Nat := if p = 2 then 2 else 1

omit [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]
  [ProperSpace K] [Fact p.Prime] localNormedAlgebra in
/-- The exponent factor is positive, so `e * s - 1` is a genuine
`q`-exponent for every positive ramification exponent `e`. -/
theorem logShellScaleExponentFactor_pos : 0 < logShellScaleExponentFactor (p := p) := by
  unfold logShellScaleExponentFactor
  split <;> norm_num

omit [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]
  [ProperSpace K] [Fact p.Prime] localNormedAlgebra in
/-- `logShellScale p` is the `s`-th power of `p`. -/
theorem logShellScale_eq_prime_pow_factor :
    logShellScale p = p ^ logShellScaleExponentFactor (p := p) := by
  unfold logShellScale logShellScaleExponentFactor
  split <;> simp

/-- The exact local `q/e/f` cardinality package that the present Mathlib
DVR interface does not yet supply. `e` is the ramification exponent
`v_K(p)`, `f` is the inertia degree, so `q = p ^ f`; the `p*`-congruence
quotient is the unit group of `Integers K / (logShellScale p)`, whose
cardinality is `q ^ (e * s - 1) * (q - 1)` with `s` as above. -/
structure LogShellQFECardinalityHypothesis (e f : Nat) : Prop where
  one_le_ramificationExponent : 1 ≤ e
  residueCard_eq_prime_pow_inertiaDegree :
    logShellResidueCard (K := K) = p ^ f
  congruenceQuotient_card_eq_residueUnits :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1)

omit [CharZero K] [CompleteSpace K] [ProperSpace K] [Fact p.Prime] localNormedAlgebra in
/-- The residue-cardinality component of the `q/e/f` package. -/
theorem logShellResidueCard_eq_prime_pow_of_qfe
    {e f : Nat} (h : LogShellQFECardinalityHypothesis (K := K) (p := p) e f) :
    logShellResidueCard (K := K) = p ^ f :=
  h.residueCard_eq_prime_pow_inertiaDegree

/-- Exact conditional `q/e/f` normalisation: if the `p*`-congruence
quotient has the residue-unit cardinality `q ^ (e * s - 1) * (q - 1)`,
then the log-shell integer index is that cardinality divided by the
torsion-unit order. This is the precise point where the missing
DVR/principal-congruence-filtration computation enters; no step assumes
the quotient cardinality. -/
theorem logShellIntegerIndex_eq_residueCard_pow_mul_sub_one_div_torsion_of_qfe
    {e f : Nat}
    (h : LogShellQFECardinalityHypothesis (K := K) (p := p) e f) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1) /
      Nat.card (CommGroup.torsion (Integers K)ˣ) := by
  have htorsion : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  have hdecomp :=
    logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex (K := K) (p := p)
  have hmul :
      Nat.card (CommGroup.torsion (Integers K)ˣ) *
          logShellIntegerIndex (K := K) (p := p) =
        logShellResidueCard (K := K) ^
            (e * logShellScaleExponentFactor (p := p) - 1) *
          (logShellResidueCard (K := K) - 1) := by
    rw [← hdecomp]
    exact h.congruenceQuotient_card_eq_residueUnits
  exact Nat.eq_div_of_mul_eq_right htorsion.ne' hmul

/-- When the torsion order divides `q - 1`, the quotient splits as
`q ^ (e * s - 1)` times the residue-unit correction
`(q - 1) / #torsion`. This is a genuine factorisation of the index, not a
definition of the correction. -/
theorem logShellIntegerIndex_eq_residueCard_pow_mul_div_of_torsion_dvd_sub_one
    {e f : Nat}
    (h : LogShellQFECardinalityHypothesis (K := K) (p := p) e f)
    (hdiv : Nat.card (CommGroup.torsion (Integers K)ˣ) ∣
      logShellResidueCard (K := K) - 1) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1) *
        ((logShellResidueCard (K := K) - 1) /
          Nat.card (CommGroup.torsion (Integers K)ˣ)) := by
  have htorsion : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  rw [logShellIntegerIndex_eq_residueCard_pow_mul_sub_one_div_torsion_of_qfe h]
  exact Nat.mul_div_assoc _ hdiv

/-- The correction factor in the previous theorem is exactly one iff the
torsion-unit order is the full residue-unit count `q - 1`. Together with
the divisibility hypothesis this is the precise condition under which the
index has the pure form `q ^ (e * s - 1)`. -/
theorem logShellResidueUnitTorsionCorrection_eq_one_iff
    (hdiv : Nat.card (CommGroup.torsion (Integers K)ˣ) ∣
      logShellResidueCard (K := K) - 1) :
    (logShellResidueCard (K := K) - 1) /
        Nat.card (CommGroup.torsion (Integers K)ˣ) = 1 ↔
      Nat.card (CommGroup.torsion (Integers K)ˣ) =
        logShellResidueCard (K := K) - 1 := by
  have htorsion : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  have hqsub : 0 < logShellResidueCard (K := K) - 1 :=
    Nat.sub_pos_of_lt (one_lt_logShellResidueCard (K := K) (p := p))
  constructor
  · intro hcorr
    obtain ⟨c, hc⟩ := hdiv
    have hquot : (logShellResidueCard (K := K) - 1) /
        Nat.card (CommGroup.torsion (Integers K)ˣ) = c := by
      rw [hc]
      exact Nat.mul_div_cancel_left c htorsion
    rw [hquot] at hcorr
    rw [hc, hcorr, mul_one]
  · intro htorsion_eq
    rw [htorsion_eq]
    exact Nat.div_self hqsub

section CommonPrimeCompletionInstance

open LeanFormal.IUT.NumberFieldFinitePlace

variable {F : Type*} [Field F] [NumberField F]
variable (place : FinitePlaceAtPrime F p)

omit [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]
  [ProperSpace K] localNormedAlgebra in
/-- The residue field is finite for the actual common-prime completion. -/
theorem finite_logShellResidueField_commonPrimeCompletion :
    Finite (logShellResidueField (K := CommonPrimeCompletion place)) :=
  finite_logShellResidueField (K := CommonPrimeCompletion place) (p := p)

omit [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]
  [ProperSpace K] localNormedAlgebra in
/-- The residue cardinal is positive for the actual common-prime completion. -/
theorem logShellResidueCard_commonPrimeCompletion_pos :
    0 < logShellResidueCard (K := CommonPrimeCompletion place) :=
  logShellResidueCard_pos (K := CommonPrimeCompletion place) (p := p)

omit [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]
  [ProperSpace K] localNormedAlgebra in
/-- Conditional residue-power normalisation for the actual common-prime
completion, obtained by instantiating the general reduction. -/
theorem logShellIntegerIndex_commonPrimeCompletion_eq_residueCard_pow_of_powerCardHypothesis
    {a : Nat}
    (hcard : LogShellResiduePowerCardHypothesis
      (K := CommonPrimeCompletion place) (p := p) a) :
    logShellIntegerIndex (K := CommonPrimeCompletion place) (p := p) =
      logShellResidueCard (K := CommonPrimeCompletion place) ^ a :=
  logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
    (K := CommonPrimeCompletion place) (p := p) hcard

end CommonPrimeCompletionInstance

end

end LeanFormal.IUT.LocalFieldLogarithm
