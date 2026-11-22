import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceLogShellFamilyDependent
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.Data.Fin.Rev

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace Probe1270

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace

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

#check actualCapsuleContract
#check actualLogShellFamily
#check actualPolyIso

end Probe1270
