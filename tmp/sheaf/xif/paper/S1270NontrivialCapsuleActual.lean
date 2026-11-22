import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.Data.Fin.Rev

/-!
# S1270: a nondegenerate actual procession-capsule contract

For an arbitrary original input I, this file builds a
SourceProcessionCapsuleContract from actual source objects.

* The first field is the actual source theater procession selected by
  canonicalCapsuleTheaterAssignment; its theaters and prime strips are
  literally I.theaterAt and I.primeStripAt, and the family is nonconstant.
* The valuation type is the type of rational primes.  Over a rational prime
  vQ, the place type is the actual finite-place fiber
  FinitePlaceAtPrime I.initial.arithmetic.Fmod vQ.
* The shell module at an actual place is the rational span IQSpan of the
  actual local log-shell datum sourceLocalLogShellDatum.  The file proves
  that its carrier is exactly the span of the actual integralLogShell of the
  common-prime completion.
* The poly-isomorphism reverses the capsule labels and multiplies each actual
  log-shell span by 2; it is not the identity poly-isomorphism.

The tensor packet is identified, through the distribution equivalence, with
the actual tensor donor SourceLogShellActualIQTensor at every tuple of actual
places.  No one-point carrier, arbitrary module, added axiom, or unfilled field
is used.
-/

noncomputable section

open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm

universe ua uv upi umon ui

/-- Multiplication by a nonzero rational is a linear equivalence of a rational
submodule of a field. -/
def actualRatSmulEquiv {K : Type*} [Field K] [CharZero K]
    (c : ℚ) (hc : c ≠ 0) (M : Submodule ℚ K) : M ≃ₗ[ℚ] M where
  toFun x := ⟨c • (x : K), M.smul_mem c x.property⟩
  invFun x := ⟨c⁻¹ • (x : K), M.smul_mem c⁻¹ x.property⟩
  left_inv x := by
    ext
    simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv x := by
    ext
    simp [smul_smul, mul_inv_cancel₀ hc]
  map_add' x y := by
    ext
    simp [smul_add]
  map_smul' a x := by
    ext
    simp [smul_smul, mul_comm]

/-- The nonarchimedean valuations of the rational field. -/
abbrev ActualValuation : Type := {p : ℕ // p.Prime}

theorem actualValuation_five_ne_seven :
    (⟨5, by norm_num⟩ : ActualValuation) ≠ ⟨7, by norm_num⟩ := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num at hv

/-- The valuation type is not a one-point index. -/
theorem actualValuation_nontrivial : Nontrivial ActualValuation where
  exists_pair_ne :=
    ⟨⟨5, by norm_num⟩, ⟨7, by norm_num⟩, actualValuation_five_ne_seven⟩

variable {l : PrimeGeFive} {V : Type uv}

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual finite-place fiber over a rational valuation. -/
def actualPlace : ActualValuation → Type ua :=
  fun vQ => FinitePlaceAtPrime I.initial.arithmetic.Fmod vQ.1

/-- The actual local log-shell datum at an actual place. -/
abbrev actualLocalLogShellDatum (vQ : ActualValuation) (v : actualPlace I vQ) :
    SourceLogShellDatum :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  sourceLocalLogShellDatum (p := vQ.1) v

/-- The actual integral log-shell at an actual place. -/
abbrev actualIntegralLogShell (vQ : ActualValuation) (v : actualPlace I vQ) :
    AddSubgroup (CommonPrimeCompletion v) :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The actual log-shell family: at every capsule label, rational valuation,
and actual finite place, the rational span of the actual local log-shell. -/
noncomputable def actualLogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℚ (actualPlace I) j where
  Shell := fun _ vQ v => (actualLocalLogShellDatum I vQ v).IQSpan
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The actual poly-isomorphism: reverse the capsule labels and multiply each
actual log-shell span by 2. -/
noncomputable def actualPolyIso (j : Nat) :
    PolyIsoAction (actualLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun _ vQ v => actualRatSmulEquiv (2 : ℚ) (by norm_num) _

/-- The full nondegenerate actual capsule contract. -/
noncomputable def actualCapsuleContract :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, 0, 0, ua, ua} ℚ l V I where
  procession := (canonicalCapsuleTheaterAssignment I 0).toProcession 0
  VQ := ActualValuation
  place := actualPlace I
  fintypePlace := fun vQ =>
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  logShell := fun j => actualLogShellFamily I j.val
  polyIso := fun j => actualPolyIso I j.val

/-- The rational span of the actual local log-shell is the span of the actual
integral log-shell of the common-prime completion. -/
theorem actualIQSpan_eq_span_integralLogShell
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualLocalLogShellDatum I vQ v).IQSpan =
      Submodule.span ℚ (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  rw [SourceLogShellDatum.IQSpan,
    sourceLocalLogShellDatum_logShell_eq_integralLogShell]
  rfl

/-- The carrier type of each shell is the carrier of the span of the actual
integral log-shell. -/
theorem actualShell_eq_carrier_span
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualLogShellFamily I j).Shell i vQ v =
      ↥(Submodule.span ℚ (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v))) := by
  change ↥((actualLocalLogShellDatum I vQ v).IQSpan) = _
  rw [actualIQSpan_eq_span_integralLogShell]
  rfl

/-- The actual shell module is linearly equivalent to the rational span of the
actual integral log-shell. -/
noncomputable def actualShellLinearEquivSpan
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualLogShellFamily I j).Shell i vQ v ≃ₗ[ℚ]
      Submodule.span ℚ (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) :=
  LinearEquiv.ofEq _ _ (actualIQSpan_eq_span_integralLogShell I vQ v)

/-- The actual finite-place fiber over 5 is nonempty. -/
theorem actualPlace_five_nonempty :
    Nonempty (actualPlace I (⟨5, by norm_num⟩ : ActualValuation)) :=
  @nonempty_fullPrimePlaces I.initial.arithmetic.Fmod _ _ 5 ⟨by norm_num⟩

/-- The label permutation of the actual action is not the identity. -/
theorem actualPolyIso_labelPerm_ne_refl :
    (actualPolyIso I 1).labelPerm ≠ Equiv.refl (Capsule 1) := by
  intro h
  have h0 := congrArg (fun e : Capsule 1 ≃ Capsule 1 => e ⟨0, by norm_num⟩) h
  simp [actualPolyIso, Fin.revPerm] at h0

/-- The actual poly-isomorphism is not the identity action. -/
theorem actualPolyIso_ne_refl :
    actualPolyIso I 1 ≠ PolyIsoAction.refl (actualLogShellFamily I 1) := by
  intro h
  exact actualPolyIso_labelPerm_ne_refl I
    (congrArg PolyIsoAction.labelPerm h)

/-- The distributed tensor packet is the actual tensor donor
SourceLogShellActualIQTensor at every tuple of actual places. -/
noncomputable def actualTensorPacketEquivSource
    (j : Nat) (vQ : ActualValuation) :
    TensorPacket (actualLogShellFamily I j) vQ ≃ₗ[ℚ]
      ((t : (i : Capsule j) → actualPlace I vQ) →
        SourceLogShellActualIQTensor
          (fun i => actualLocalLogShellDatum I vQ (t i))) := by
  letI : Fintype (actualPlace I vQ) :=
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  exact tensorPacketEquiv (actualLogShellFamily I j) vQ

/-- The first field of the contract is the selected actual source procession. -/
theorem actualCapsuleContract_procession :
    (actualCapsuleContract I).procession =
      (canonicalCapsuleTheaterAssignment I 0).toProcession 0 := rfl

/-- The log-shell field is the actual family defined above. -/
theorem actualCapsuleContract_logShell
    (j : Fin (capsuleLevels l)) :
    (actualCapsuleContract I).logShell j = actualLogShellFamily I j.val := rfl

/-- The poly-isomorphism field is the actual action defined above. -/
theorem actualCapsuleContract_polyIso
    (j : Fin (capsuleLevels l)) :
    (actualCapsuleContract I).polyIso j = actualPolyIso I j.val := rfl

/-- The theater at a capsule label is the actual source theater at the selected
source index. -/
theorem actualCapsuleContract_theater
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    ((actualCapsuleContract I).procession).toPrimeStripOf.theater j i =
      I.theaterAt (Int.ofNat i.val) 0 := rfl

/-- The prime strip at a capsule label is the actual source prime strip at the
selected source index. -/
theorem actualCapsuleContract_primeStrip
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    ((actualCapsuleContract I).procession).toPrimeStripOf.primeStrip j i =
      I.primeStripAt (Int.ofNat i.val) 0 := rfl

/-- The actual theater family of the contract is nonconstant. -/
theorem actualCapsuleContract_theater_nontrivial :
    ∃ (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualCapsuleContract I).procession).toPrimeStripOf.theater j i ≠
        ((actualCapsuleContract I).procession).toPrimeStripOf.theater j i' := by
  simpa [actualCapsuleContract] using
    canonicalCapsuleTheaterAssignment.theater_nontrivial I 0

/-- The actual prime-strip family of the contract is nonconstant. -/
theorem actualCapsuleContract_primeStrip_nontrivial :
    ∃ (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualCapsuleContract I).procession).toPrimeStripOf.primeStrip j i ≠
        ((actualCapsuleContract I).procession).toPrimeStripOf.primeStrip j i' := by
  simpa [actualCapsuleContract] using
    canonicalCapsuleTheaterAssignment.primeStrip_nontrivial I 0

#print axioms actualCapsuleContract
#print axioms actualIQSpan_eq_span_integralLogShell
#print axioms actualShell_eq_carrier_span
#print axioms actualShellLinearEquivSpan
#print axioms actualPolyIso_ne_refl
#print axioms actualTensorPacketEquivSource
#print axioms actualCapsuleContract_theater_nontrivial
#print axioms actualCapsuleContract_primeStrip_nontrivial

end LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual
