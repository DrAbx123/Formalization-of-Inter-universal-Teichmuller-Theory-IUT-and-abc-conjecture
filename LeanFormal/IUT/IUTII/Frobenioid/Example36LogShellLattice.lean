/-
  # The actual local log-shell lattice at the concrete Gaussian place

  Task task-76 (Foundation F6c).  At the actual finite place of the concrete
  Example 3.6 carrier (the rational prime 5 in Q(i)) this module constructs:

  1. The actual local field concreteLogShellField = NormalizedCompletion
     concretePlace, the normalized completion of Q(i) at the concrete place,
     with its normed Q_5-algebra structure and its p-adic logarithm log1p.
  2. The principal-unit log-shell principalUnitLogShell: the actual image of
     the p-adic logarithm on the actual principal units 1 + m_v of the
     completion integers.  It is an additive subgroup, identified with the set
     of logarithms of principal units (unitLog = log1p on principal units).
  3. The tree's actual integral log-shell lattice integralLogShellLattice, its
     finite/free Z_5-lattice structure, its exact integer index
     logShellIntegerIndex, its Haar measure formula and relative Haar log
     discrepancy, and the sharp inertial bounds of IUT IV Proposition 1.2(i),
     all instantiated at this concrete local field.

  The relation between the principal-unit shell and the tree's scaled shell is
  proved: dividing a principal-unit logarithm by the paper's scale factor
  logShellScale p lies in the actual integral log-shell.  The principal-unit
  shell is contained in the unscaled unit-log lattice of IUT IV and hence
  satisfies the paper's upper B bound.

  The realification of the task-21 finite-place unit value kernel at this place
  is the actual normalized local log-volume -nu * log(#(O_F / v)).  It is
  compared exactly with the requested finite-place log-volume
  concretePlaceLogVolume nu = -nu * log q, where q = gaussianFiveThetaQ = 1/5:
  their sum is the explicit residue correction nu * log(5 / #(O_F / v)).  In
  particular, if the residue cardinality is 5, the realification is exactly
  minus the requested log-volume.  The residue-cardinality identity is not
  assumed; the exact difference is stated instead.

  ## Frozen source card

  The tree has the actual local log-shell lattice, its index and Haar data, but
  it does not have the source's Theta and Frobenius action on a source log-shell
  carrier (the arithmetic Frobenius action on the log-shell used in the
  Theta-link and log-volume comparison).  This is frozen as
  SourceLogShellFrobeniusCard, with no inhabitant constructed here and no fake
  lattice or index claimed.  No theta-pilot/q-pilot/Tate claim is made.

  Source correspondence: IUT III, Definition 1.1 and Remark 1.2.2 (log-shell),
  Proposition 1.2 (log-shell lattice and Haar measure); IUT IV, Proposition
  1.2(i) (sharp log-shell bounds); IUT III, Example 3.6 (concrete local data).
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace LogShellLattice

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open IsDedekindDomain
open scoped Pointwise

local instance gaussianPolynomialIrreducibleFactLogShell :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactLogShell : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactLogShell (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The actual local field and its principal-unit log-shell -/

/-- The actual local field at the concrete place: the normalized completion of
Q(i) at concretePlace. -/
abbrev concreteLogShellField := NormalizedCompletion concretePlace

/-- The actual rational prime below the concrete place. -/
abbrev concreteRationalPrime : ℕ := (completionRationalPrime concretePlace).val

local instance concreteLogShellFieldMeasurableSpace :
    MeasurableSpace concreteLogShellField :=
  borel concreteLogShellField

local instance concreteLogShellFieldBorelSpace :
    BorelSpace concreteLogShellField :=
  ⟨rfl⟩

/-- The concrete height-one prime of the local log-shell is the maximal ideal of
the concrete place. -/
theorem concreteHeightOneSpectrum_eq_maximalIdeal :
    concreteHeightOneSpectrum = concretePlace.maximalIdeal :=
  rfl

/-- The principal-unit log-shell: the actual image of the p-adic logarithm on
the actual principal units of the completion integers. -/
noncomputable def principalUnitLogShell : AddSubgroup concreteLogShellField where
  carrier := Set.range (fun u : principalUnits (K := concreteLogShellField) =>
    unitLog (K := concreteLogShellField) (u : (Integers concreteLogShellField)ˣ))
  zero_mem' := ⟨1, by
    simpa using unitLog_one (K := concreteLogShellField) (p := concreteRationalPrime)⟩
  add_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, by
      simpa only [Subgroup.coe_mul] using
        unitLog_mul (K := concreteLogShellField) (p := concreteRationalPrime)
          (u : (Integers concreteLogShellField)ˣ)
          (v : (Integers concreteLogShellField)ˣ)⟩
  neg_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u⁻¹, by
      simpa only [Subgroup.coe_inv] using
        unitLog_inv (K := concreteLogShellField) (p := concreteRationalPrime)
          (u : (Integers concreteLogShellField)ˣ)⟩

/-- Membership in the principal-unit log-shell is membership of the actual
logarithm of a principal unit. -/
theorem principalUnitLogShell_mem_iff (x : concreteLogShellField) :
    x ∈ principalUnitLogShell ↔
      ∃ u : principalUnits (K := concreteLogShellField),
        unitLog (K := concreteLogShellField)
          (u : (Integers concreteLogShellField)ˣ) = x :=
  Iff.rfl

/-- The actual logarithm of a principal unit is the analytic logarithm log1p of
the principal-unit element. -/
theorem unitLog_principalUnit_eq_log1p
    (u : principalUnits (K := concreteLogShellField)) :
    unitLog (K := concreteLogShellField)
        (u : (Integers concreteLogShellField)ˣ) =
      log1p (((u : (Integers concreteLogShellField)ˣ).val : concreteLogShellField) - 1) :=
  unitLog_eq_log1p (K := concreteLogShellField) (p := concreteRationalPrime)
    (u := (u : (Integers concreteLogShellField)ˣ)) u.property

/-- The principal-unit log-shell is exactly the image of the p-adic logarithm
log1p on the principal units. -/
theorem coe_principalUnitLogShell_eq_range_log1p :
    (principalUnitLogShell : Set concreteLogShellField) =
      Set.range (fun u : principalUnits (K := concreteLogShellField) =>
        log1p (((u : (Integers concreteLogShellField)ˣ).val : concreteLogShellField) - 1)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := (principalUnitLogShell_mem_iff x).mp hx
    exact ⟨u, (unitLog_principalUnit_eq_log1p u).symm⟩
  · rintro ⟨u, rfl⟩
    exact (principalUnitLogShell_mem_iff _).mpr ⟨u, unitLog_principalUnit_eq_log1p u⟩

/-! ## 2. Relation to the tree's integral log-shell and unit-log lattice -/

/-- Dividing a principal-unit logarithm by the paper's scale factor gives an
element of the actual integral log-shell. -/
theorem inv_logShellScale_mul_mem_integralLogShell
    {x : concreteLogShellField} (hx : x ∈ principalUnitLogShell) :
    ((logShellScale concreteRationalPrime : concreteLogShellField)⁻¹) * x ∈
      integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) := by
  obtain ⟨u, rfl⟩ := (principalUnitLogShell_mem_iff x).mp hx
  exact ⟨(u : (Integers concreteLogShellField)ˣ), rfl⟩

/-- The scaled principal-unit log-shell is contained in the actual integral
log-shell of the tree. -/
theorem inv_logShellScale_smul_principalUnitLogShell_subset :
    ((logShellScale concreteRationalPrime : concreteLogShellField)⁻¹) •
        (principalUnitLogShell : Set concreteLogShellField) ⊆
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField) := by
  rintro _ ⟨x, hx, rfl⟩
  exact inv_logShellScale_mul_mem_integralLogShell hx

/-- The principal-unit log-shell is contained in the unscaled unit-log lattice
of IUT IV. -/
theorem principalUnitLogShell_subset_unitLogLattice :
    (principalUnitLogShell : Set concreteLogShellField) ⊆
      (unitLogLattice (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField) := by
  rw [coe_unitLogLattice_eq_range]
  rintro _ ⟨u, rfl⟩
  exact ⟨(u : (Integers concreteLogShellField)ˣ), rfl⟩

/-! ## 3. Lattice, index, Haar and sharp-bound structure of the tree -/

/-- The actual integral log-shell lattice is a finite Z_5-module. -/
theorem concrete_integralLogShellLattice_finite :
    Module.Finite ℤ_[concreteRationalPrime]
      (integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime)) :=
  inferInstance

/-- The actual integral log-shell lattice is free over Z_5. -/
theorem concrete_integralLogShellLattice_free :
    Module.Free ℤ_[concreteRationalPrime]
      (integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime)) :=
  inferInstance

/-- The rank of the actual integral log-shell lattice is the Q_5-dimension of
the local field. -/
theorem concrete_finrank_integralLogShellLattice :
    Module.finrank ℤ_[concreteRationalPrime]
        (integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime)) =
      Module.finrank ℚ_[concreteRationalPrime] concreteLogShellField :=
  finrank_integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The actual integral log-shell lattice spans the local field over Q_5. -/
theorem concrete_span_integralLogShellLattice_eq_top :
    Submodule.span ℚ_[concreteRationalPrime]
        (integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime) :
          Set concreteLogShellField) = ⊤ :=
  span_padic_integralLogShellLattice_eq_top (K := concreteLogShellField)
    (p := concreteRationalPrime)

/-- The valuation integers are an actual sublattice of the integral log-shell
lattice. -/
theorem concrete_valuationIntegerLattice_le_integralLogShellLattice :
    valuationIntegerLattice (K := concreteLogShellField) (p := concreteRationalPrime) ≤
      integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime) :=
  valuationIntegerLattice_le_integralLogShellLattice (K := concreteLogShellField)
    (p := concreteRationalPrime)

/-- The actual integral log-shell is compact. -/
theorem concrete_isCompact_integralLogShell :
    IsCompact (integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime) : Set concreteLogShellField) :=
  isCompact_integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The actual integral log-shell is open in the local field. -/
theorem concrete_isOpen_integralLogShell :
    IsOpen (integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime) : Set concreteLogShellField) :=
  isOpen_integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The actual integer ring is contained in the actual integral log-shell. -/
theorem concrete_integers_subset_integralLogShell :
    (Integers concreteLogShellField : Set concreteLogShellField) ⊆
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField) :=
  integers_subset_integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The actual log-shell integer index is positive. -/
theorem concrete_logShellIntegerIndex_pos :
    0 < logShellIntegerIndex (K := concreteLogShellField) (p := concreteRationalPrime) :=
  logShellIntegerIndex_pos (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The actual log-shell integer index is the congruence-quotient order divided
by the torsion-unit order. -/
theorem concrete_logShellIntegerIndex_eq_card_div_torsion :
    logShellIntegerIndex (K := concreteLogShellField) (p := concreteRationalPrime) =
      Nat.card ((Integers concreteLogShellField)ˣ ⧸
          logShellCongruenceUnits (K := concreteLogShellField) (p := concreteRationalPrime)) /
        Nat.card (CommGroup.torsion (Integers concreteLogShellField)ˣ) :=
  logShellIntegerIndex_eq_card_div_torsion (K := concreteLogShellField)
    (p := concreteRationalPrime)

/-- The exact cardinal decomposition of the congruence quotient by the torsion
units and the log-shell integer index. -/
theorem concrete_logShellCongruenceQuotient_card_eq_torsion_mul_index :
    Nat.card ((Integers concreteLogShellField)ˣ ⧸
        logShellCongruenceUnits (K := concreteLogShellField) (p := concreteRationalPrime)) =
      Nat.card (CommGroup.torsion (Integers concreteLogShellField)ˣ) *
        logShellIntegerIndex (K := concreteLogShellField) (p := concreteRationalPrime) :=
  logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex
    (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The Haar measure of the actual integral log-shell is the integer index times
the Haar measure of the integers. -/
theorem concrete_measure_integralLogShell_eq_index_mul
    (μ : MeasureTheory.Measure concreteLogShellField)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField) =
      (logShellIntegerIndex (K := concreteLogShellField) (p := concreteRationalPrime) :
          ENNReal) *
        μ (Integers concreteLogShellField : Set concreteLogShellField) :=
  measure_integralLogShell_eq_index_mul (K := concreteLogShellField)
    (p := concreteRationalPrime) μ

/-- The relative Haar log discrepancy of the actual integral log-shell is
nonnegative. -/
theorem concrete_integralLogShellDiscrepancy_nonneg :
    0 ≤ integralLogShellDiscrepancy (K := concreteLogShellField)
      (p := concreteRationalPrime) :=
  integralLogShellDiscrepancy_nonneg (K := concreteLogShellField) (p := concreteRationalPrime)

/-- The relative Haar log discrepancy is the log of the congruence-quotient order
minus the log of the torsion-unit order. -/
theorem concrete_integralLogShellDiscrepancy_eq_log_congruence_sub_log_torsion :
    integralLogShellDiscrepancy (K := concreteLogShellField) (p := concreteRationalPrime) =
      Real.log (Nat.card ((Integers concreteLogShellField)ˣ ⧸
          logShellCongruenceUnits (K := concreteLogShellField) (p := concreteRationalPrime)) : ℝ) -
        Real.log (Nat.card (CommGroup.torsion (Integers concreteLogShellField)ˣ) : ℝ) :=
  integralLogShellDiscrepancy_eq_log_congruence_sub_log_torsion (K := concreteLogShellField)
    (p := concreteRationalPrime)

/-- IUT IV Proposition 1.2(i), upper inclusion on the unscaled unit-log lattice of
the actual local field. -/
theorem concrete_unitLogLattice_le_padicFractionalLattice_neg_paperB :
    unitLogLattice (K := concreteLogShellField) (p := concreteRationalPrime) ≤
      padicFractionalLattice (K := concreteLogShellField) (p := concreteRationalPrime)
        (-(logShellPaperBExponent concreteRationalPrime
          (logShellRamificationExponent (K := concreteLogShellField)
            (p := concreteRationalPrime)))) :=
  unitLogLattice_le_padicFractionalLattice_neg_paperB (K := concreteLogShellField)
    (p := concreteRationalPrime)

/-- IUT IV Proposition 1.2(i), lower inclusion on the unscaled unit-log lattice of
the actual local field. -/
theorem concrete_padicFractionalLattice_paperA_le_unitLogLattice :
    padicFractionalLattice (K := concreteLogShellField) (p := concreteRationalPrime)
        (logShellPaperAExponent concreteRationalPrime
          (logShellRamificationExponent (K := concreteLogShellField)
            (p := concreteRationalPrime))) ≤
      unitLogLattice (K := concreteLogShellField) (p := concreteRationalPrime) :=
  padicFractionalLattice_paperA_le_unitLogLattice (K := concreteLogShellField)
    (p := concreteRationalPrime)

/-- The principal-unit log-shell satisfies the paper's upper B bound. -/
theorem principalUnitLogShell_subset_padicFractionalLattice_neg_paperB :
    (principalUnitLogShell : Set concreteLogShellField) ⊆
      (padicFractionalLattice (K := concreteLogShellField) (p := concreteRationalPrime)
        (-(logShellPaperBExponent concreteRationalPrime
          (logShellRamificationExponent (K := concreteLogShellField)
            (p := concreteRationalPrime)))) : Set concreteLogShellField) := by
  intro x hx
  exact concrete_unitLogLattice_le_padicFractionalLattice_neg_paperB
    (principalUnitLogShell_subset_unitLogLattice hx)

/-! ## 4. Realification versus -nu log q and the task-21 unit value kernel -/

/-- The requested finite-place log-volume of an exponent nu at the concrete
place: -nu * log q, with q = gaussianFiveThetaQ = 1/5. -/
noncomputable def concretePlaceLogVolume (nu : ℤ) : ℝ :=
  -((nu : ℝ) * Real.log gaussianFiveThetaQ)

/-- The logarithm of the actual local q-parameter is -log 5. -/
theorem concretePlace_log_gaussianFiveThetaQ :
    Real.log gaussianFiveThetaQ = -Real.log 5 :=
  gaussianFiveThetaQ_log

/-- The requested log-volume is nu * log 5. -/
theorem concretePlaceLogVolume_eq (nu : ℤ) :
    concretePlaceLogVolume nu = (nu : ℝ) * Real.log 5 := by
  unfold concretePlaceLogVolume
  rw [concretePlace_log_gaussianFiveThetaQ]
  ring

/-- The realification of the task-21 finite-place unit value kernel at the
concrete place is minus the classical exponent times the logarithm of the actual
residue-field cardinality. -/
theorem concretePlace_unitValueKernel_realification
    (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum) :
    (finitePlaceUnitValueKernel (F := GaussianField)
      concreteHeightOneSpectrum).realification x =
      -((completionValuationExponent concreteHeightOneSpectrum x : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := GaussianField)
          concreteHeightOneSpectrum : ℝ))) := by
  simpa only [neg_mul] using
    finitePlaceUnitValueKernel_realification (F := GaussianField)
      concreteHeightOneSpectrum x

/-- The exact relation between the task-21 realification and the requested
log-volume -nu log q: their sum is the residue correction
nu * log(5 / #(O_F / v)). -/
theorem concretePlace_realification_add_logVolume_eq_residueCorrection
    (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum) :
    (finitePlaceUnitValueKernel (F := GaussianField)
        concreteHeightOneSpectrum).realification x +
      concretePlaceLogVolume (completionValuationExponent concreteHeightOneSpectrum x) =
        (completionValuationExponent concreteHeightOneSpectrum x : ℝ) *
          Real.log ((5 : ℝ) /
            (finitePlaceResidueCardinality (F := GaussianField)
              concreteHeightOneSpectrum : ℝ)) := by
  rw [concretePlace_unitValueKernel_realification,
    concretePlaceLogVolume_eq]
  have hpos : (0 : ℝ) < (finitePlaceResidueCardinality (F := GaussianField)
      concreteHeightOneSpectrum : ℝ) := by
    exact_mod_cast finitePlaceResidueCardinality_pos (F := GaussianField)
      concreteHeightOneSpectrum
  rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) hpos.ne']
  ring

/-- If the actual residue cardinality at the concrete place is 5, the task-21
realification is exactly minus the requested log-volume -nu log q. -/
theorem concretePlace_realification_eq_neg_logVolume_of_residueCard_five
    (hcard : finitePlaceResidueCardinality (F := GaussianField)
      concreteHeightOneSpectrum = 5)
    (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum) :
    (finitePlaceUnitValueKernel (F := GaussianField)
      concreteHeightOneSpectrum).realification x =
      - concretePlaceLogVolume
        (completionValuationExponent concreteHeightOneSpectrum x) := by
  have h := concretePlace_realification_add_logVolume_eq_residueCorrection x
  rw [hcard] at h
  norm_num at h
  rw [concretePlace_unitValueKernel_realification]
  linarith

/-! ## 5. Frozen source log-shell carrier/Frobenius-action card -/

/-- **Frozen card for the missing source log-shell carrier and Frobenius
action.**  The tree constructs the actual local log-shell lattice, its integer
index and its Haar data, and this file identifies the principal-unit image and
the task-21 realification.  The source's log-shell as a Frobenius-equivariant
carrier with the arithmetic Frobenius action used in the Theta-link and
log-volume comparison is not constructed in the tree.  The card records the
shape of that missing data: a carrier embedded injectively in the actual local
field, a Frobenius self-map, and the p-power Frobenius action law.  No
inhabitant is constructed in this file and no theorem consumes one; in
particular no fake lattice, index or Frobenius action is substituted. -/
structure SourceLogShellFrobeniusCard (l : PrimeGeFive) where
  /-- The source log-shell carrier. -/
  LogShell : Type
  /-- Its embedding in the actual local field. -/
  toLocalField : LogShell → concreteLogShellField
  /-- The embedding is injective. -/
  toLocalField_injective : Function.Injective toLocalField
  /-- The arithmetic Frobenius self-map on the source log-shell. -/
  frobenius : LogShell → LogShell
  /-- The p-power Frobenius action law on the embedded carrier. -/
  frobenius_action : ∀ x : LogShell,
    toLocalField (frobenius x) =
      (concreteRationalPrime : concreteLogShellField) * toLocalField x
  /-- The source Frobenius action is genuinely nontrivial. -/
  frobenius_nontrivial : ∃ x : LogShell, frobenius x ≠ x

/-! ## 6. Summary -/

/-- **Summary of the actual local log-shell lattice at the concrete place.**
The principal-unit log-shell is an actual additive subgroup equal to the image
of the p-adic logarithm log1p on principal units; scaled by the paper factor it
lies in the actual integral log-shell, and it is contained in the unscaled
unit-log lattice and its upper B fractional bound.  The tree's integral
log-shell lattice is finite, free and of full rank, with positive integer index,
Haar measure formula and nonnegative relative log discrepancy, and the sharp
IUT IV bounds are instantiated.  The task-21 realification satisfies the exact
residue-correction identity against -nu log q, and the missing source
log-shell/Frobenius carrier is frozen as a card. -/
theorem example36LogShellLattice_summary :
    (∀ (x : concreteLogShellField), x ∈ principalUnitLogShell ↔
      ∃ u : principalUnits (K := concreteLogShellField),
        unitLog (K := concreteLogShellField)
          (u : (Integers concreteLogShellField)ˣ) = x) ∧
    (∀ (x : concreteLogShellField), x ∈ principalUnitLogShell →
      ((logShellScale concreteRationalPrime : concreteLogShellField)⁻¹) * x ∈
        integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) ∧
    (0 < logShellIntegerIndex (K := concreteLogShellField) (p := concreteRationalPrime)) ∧
    (Module.finrank ℤ_[concreteRationalPrime]
        (integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime)) =
      Module.finrank ℚ_[concreteRationalPrime] concreteLogShellField) ∧
    (∀ x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum,
      (finitePlaceUnitValueKernel (F := GaussianField)
          concreteHeightOneSpectrum).realification x +
        concretePlaceLogVolume
          (completionValuationExponent concreteHeightOneSpectrum x) =
        (completionValuationExponent concreteHeightOneSpectrum x : ℝ) *
          Real.log ((5 : ℝ) /
            (finitePlaceResidueCardinality (F := GaussianField)
              concreteHeightOneSpectrum : ℝ))) :=
  ⟨principalUnitLogShell_mem_iff,
    fun _ hx => inv_logShellScale_mul_mem_integralLogShell hx,
    concrete_logShellIntegerIndex_pos,
    concrete_finrank_integralLogShellLattice,
    fun x => concretePlace_realification_add_logVolume_eq_residueCorrection x⟩

end

end LogShellLattice
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the actual local log-shell lattice at the concrete Gaussian
place.  The actual p-adic completion of Q(i) at the concrete place is given the
normalized Q_5-normed structure; the principal-unit log-shell is the actual
image of the p-adic logarithm log1p on principal units and is an additive
subgroup; the tree's integral log-shell lattice, its finite/free Z_5-lattice
structure, integer index, Haar measure formula, relative Haar log discrepancy
and the sharp IUT IV Proposition 1.2(i) bounds are instantiated; the task-21
unit value kernel realification is compared exactly with -nu log q (the
difference is the residue correction nu log(5/#res)); the source
log-shell/Frobenius carrier is frozen as SourceLogShellFrobeniusCard.  No fake
lattice, index or Frobenius action is claimed. -/
def example36LogShellLattice : Obligation :=
  { id := "IUT-II.example36-log-shell-lattice"
    source :=
      "IUT III, Definition 1.1 and Remark 1.2.2 (log-shell), Proposition 1.2 " ++
        "(log-shell lattice and Haar measure); IUT IV, Proposition 1.2(i) " ++
        "(sharp log-shell bounds); IUT III, Example 3.6 (concrete local data)"
    status := VerificationStatus.interface
    note :=
      "Built at the actual finite place of the concrete Example 3.6 carrier " ++
        "(the concrete place of Q(i), actual rational prime 5): the actual " ++
        "local field is concreteLogShellField = NormalizedCompletion " ++
        "concretePlace with its normed Q_5-algebra structure.  The " ++
        "principal-unit log-shell principalUnitLogShell is the actual image of " ++
        "the p-adic logarithm on the actual principal units 1 + m_v of the " ++
        "completion integers; it is an additive subgroup " ++
        "(principalUnitLogShell_mem_iff) and is identified with the image of " ++
        "log1p on principal units (unitLog_principalUnit_eq_log1p, " ++
        "coe_principalUnitLogShell_eq_range_log1p).  Dividing a principal-unit " ++
        "logarithm by the paper factor logShellScale p lands in the actual " ++
        "integral log-shell (inv_logShellScale_mul_mem_integralLogShell), and " ++
        "the principal shell is contained in the tree's unscaled unit-log " ++
        "lattice (principalUnitLogShell_subset_unitLogLattice) and hence in " ++
        "the paper's upper B fractional lattice.  Tree structure instantiated: " ++
        "integral log-shell lattice finite/free/full rank/spanning/inclusion " ++
        "with valuation integers/compactness/openness/integral containment; " ++
        "positive logShellIntegerIndex and its exact cardinal decomposition by " ++
        "the congruence quotient and torsion units; the Haar measure formula " ++
        "and nonnegative relative Haar log discrepancy; and both sharp " ++
        "IUT IV Proposition 1.2(i) inclusions on the unscaled unit-log " ++
        "lattice.  Task-21 unit value kernel: the realification at the " ++
        "concrete place is -nu log(#res) " ++
        "(concretePlace_unitValueKernel_realification), and its exact " ++
        "relation to the requested log-volume -nu log q (q = gaussianFiveThetaQ " ++
        "= 1/5) is realification + logVolume = nu log(5/#res) " ++
        "(concretePlace_realification_add_logVolume_eq_residueCorrection); if " ++
        "#res = 5 then realification = -logVolume " ++
        "(concretePlace_realification_eq_neg_logVolume_of_residueCard_five).  " ++
        "The residue cardinality identity itself is not assumed; the exact " ++
        "difference is stated.  NOT provided: the source log-shell carrier " ++
        "with its arithmetic Frobenius action used in the Theta-link and " ++
        "log-volume comparison; frozen as SourceLogShellFrobeniusCard with no " ++
        "inhabitant and no substitution.  No theta-pilot/q-pilot/Tate claim."
    dependsOn :=
      [ "IUT-II.example36-source-theater-carrier",
        "IUT-II.example36-prime-strip-bridge",
        "IUT-III.local-log-shell-lattice",
        "IUT-III.log-shell-index-arithmetic",
        "IUT-III.log-shell-haar-index",
        "IUT-IV.log-shell-sharp-bounds" ] }

end LeanFormal.IUT.Audit
