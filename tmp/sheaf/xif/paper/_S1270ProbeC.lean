import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.Data.Fin.Rev

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace Probe1270C

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

def ratSmulEquiv {K : Type*} [Field K] [CharZero K]
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

abbrev ActualValuation : Type := {p : ℕ // p.Prime}

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

def actualPlace : ActualValuation → Type ua :=
  fun vQ => FinitePlaceAtPrime I.initial.arithmetic.Fmod vQ.1

noncomputable def actualLogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℚ (actualPlace I) j where
  Shell := fun i vQ v =>
    letI : Fact vQ.1.Prime := ⟨vQ.2⟩
    (sourceLocalLogShellDatum (p := vQ.1) v).IQSpan
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

noncomputable def actualPolyIso (j : Nat) :
    PolyIsoAction (actualLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun i vQ v => ratSmulEquiv (2 : ℚ) (by norm_num) _

noncomputable def actualCapsuleContract :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, 0, 0, ua, ua} ℚ l V I where
  procession := (canonicalCapsuleTheaterAssignment I 0).toProcession 0
  VQ := ActualValuation
  place := actualPlace I
  fintypePlace := fun vQ =>
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  logShell := fun j => actualLogShellFamily I j.val
  polyIso := fun j => actualPolyIso I j.val

theorem actualShell_eq_span_integralLogShell
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualLogShellFamily I j).Shell i vQ v =
      Submodule.span ℚ
        (((integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1) :
          AddSubgroup (CommonPrimeCompletion v)) : Set (CommonPrimeCompletion v))) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  change (sourceLocalLogShellDatum (p := vQ.1) v).IQSpan = _
  rw [SourceLogShellDatum.IQSpan,
    sourceLocalLogShellDatum_logShell_eq_integralLogShell]

theorem actualValuation_five_ne_seven :
    (⟨5, by norm_num⟩ : ActualValuation) ≠ ⟨7, by norm_num⟩ := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num at hv

theorem actualPlace_five_nonempty :
    Nonempty (actualPlace I (⟨5, by norm_num⟩ : ActualValuation)) :=
  @nonempty_fullPrimePlaces I.initial.arithmetic.Fmod _ _ 5 ⟨by norm_num⟩

theorem actualPolyIso_labelPerm_ne_refl :
    (actualPolyIso I 1).labelPerm ≠ Equiv.refl (Capsule 1) := by
  intro h
  have h0 := congrArg (fun e : Capsule 1 ≃ Capsule 1 => e ⟨0, by norm_num⟩) h
  simp [actualPolyIso, Fin.revPerm] at h0

noncomputable def actualTensorPacketEquivSource
    (j : Nat) (vQ : ActualValuation) :
    TensorPacket (actualLogShellFamily I j) vQ ≃ₗ[ℚ]
      ((t : (i : Capsule j) → actualPlace I vQ) →
        SourceLogShellActualIQTensor
          (fun i => sourceLocalLogShellDatum (p := vQ.1) (t i))) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  exact tensorPacketEquiv (actualLogShellFamily I j) vQ

theorem actualCapsuleContract_procession :
    (actualCapsuleContract I).procession =
      (canonicalCapsuleTheaterAssignment I 0).toProcession 0 := rfl

theorem actualCapsuleContract_theater_nontrivial :
    ∃ (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualCapsuleContract I).procession).toPrimeStripOf.theater j i ≠
        ((actualCapsuleContract I).procession).toPrimeStripOf.theater j i' := by
  simpa [actualCapsuleContract] using
    canonicalCapsuleTheaterAssignment.theater_nontrivial I 0

#print axioms actualCapsuleContract
#print axioms actualShell_eq_span_integralLogShell
#print axioms actualPolyIso_labelPerm_ne_refl
#print axioms actualTensorPacketEquivSource

end Probe1270C
