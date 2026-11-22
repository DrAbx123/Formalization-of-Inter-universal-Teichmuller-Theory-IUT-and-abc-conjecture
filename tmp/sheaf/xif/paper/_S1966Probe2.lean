import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open scoped BigOperators

namespace Probe1966

/-! ## labels -/

abbrev ThetaLabel (l : PrimeGeFive) := Fin (lStar l.value)

theorem one_lt_lStar (l : PrimeGeFive) : 1 < lStar l.value := by
  have h5 : 5 ≤ l.value := l.ge_five
  unfold lStar
  omega

def thetaZero (l : PrimeGeFive) : ThetaLabel l := ⟨0, by have := one_lt_lStar l; omega⟩

def thetaOne (l : PrimeGeFive) : ThetaLabel l := ⟨1, by exact one_lt_lStar l⟩

theorem thetaZero_ne_thetaOne (l : PrimeGeFive) : thetaZero l ≠ thetaOne l := by
  intro h
  have h' := congrArg (fun x : ThetaLabel l => (x.1 : Nat)) h
  simp [thetaZero, thetaOne] at h'

def thetaToSigned (l : PrimeGeFive) (j : ThetaLabel l) : SignedLabel l.value :=
  ⟨(j.1 : Int) + 1, by
    have hj : j.1 < lStar l.value := j.2
    have hj0 : (0 : Int) ≤ (j.1 : Int) := by exact_mod_cast Nat.zero_le j.1
    have hk : (1 : Int) ≤ (lStar l.value : Int) := by
      exact_mod_cast le_of_lt (one_lt_lStar l)
    constructor
    · omega
    · have hle : j.1 + 1 ≤ lStar l.value := Nat.succ_le_of_lt hj
      exact_mod_cast hle⟩

theorem thetaToSigned_injective (l : PrimeGeFive) :
    Function.Injective (thetaToSigned l) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg (fun x : SignedLabel l.value => (x.1 : Int)) h
  simp [thetaToSigned] at h'
  omega

@[simp] theorem thetaToSigned_thetaZero (l : PrimeGeFive) :
    (thetaToSigned l (thetaZero l)).1 = 1 := rfl

@[simp] theorem thetaToSigned_thetaOne (l : PrimeGeFive) :
    (thetaToSigned l (thetaOne l)).1 = 2 := rfl

/-! ## Gaussian weight -/

def gaussianWeight (p : Nat) (l : PrimeGeFive) : ThetaLabel l → Real :=
  fun j => ((j.1 + 1 : Nat) : Real) ^ 2 * Real.log p

theorem gaussianWeight_pos (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive)
    (j : ThetaLabel l) : 0 < gaussianWeight p l j := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hj : (0 : Real) < ((j.1 + 1 : Nat) : Real) := by positivity
  exact mul_pos (sq_pos_of_pos hj) hlog

theorem gaussianWeight_thetaZero (p : Nat) (l : PrimeGeFive) :
    gaussianWeight p l (thetaZero l) = Real.log p := by
  simp [gaussianWeight, thetaZero]

theorem gaussianWeight_ne_zero (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    gaussianWeight p l ≠ 0 := by
  intro h
  have h0 := congrFun h (thetaZero l)
  rw [gaussianWeight_thetaZero] at h0
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  exact hlog h0

def gaussianProfile (p : Nat) (l : PrimeGeFive) (c : NNReal) : ThetaLabel l → Real :=
  fun j => (c : Real) * gaussianWeight p l j

@[simp] theorem gaussianProfile_zero (p : Nat) (l : PrimeGeFive) :
    gaussianProfile p l 0 = 0 := by
  funext j
  simp [gaussianProfile]

theorem gaussianProfile_add (p : Nat) (l : PrimeGeFive) (c d : NNReal) :
    gaussianProfile p l (c + d) = gaussianProfile p l c + gaussianProfile p l d := by
  funext j
  simp [gaussianProfile, NNReal.coe_add, add_mul]

def gaussianRay (p : Nat) (l : PrimeGeFive) : AddSubmonoid (ThetaLabel l → Real) where
  carrier := {x | ∃ c : NNReal, x = gaussianProfile p l c}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, by rw [gaussianProfile_add]⟩

theorem mem_gaussianRay_iff (p : Nat) (l : PrimeGeFive) {x : ThetaLabel l → Real} :
    x ∈ gaussianRay p l ↔ ∃ c : NNReal, x = gaussianProfile p l c := Iff.rfl

theorem gaussianWeight_mem_ray (p : Nat) (l : PrimeGeFive) :
    gaussianWeight p l ∈ gaussianRay p l := by
  refine ⟨1, ?_⟩
  funext j
  simp [gaussianProfile]

theorem gaussianProfile_injective (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Injective (gaussianProfile p l) := by
  intro c d h
  have h0 := congrFun h (thetaZero l)
  simp only [gaussianProfile, gaussianWeight_thetaZero] at h0
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have hcd : (c : Real) = (d : Real) := mul_right_cancel₀ hlog h0
  exact NNReal.coe_injective hcd

abbrev GaussianRay (p : Nat) (l : PrimeGeFive) := gaussianRay p l

def gaussianRayHom (p : Nat) (l : PrimeGeFive) : NNReal →+ gaussianRay p l where
  toFun c := ⟨gaussianProfile p l c, ⟨c, rfl⟩⟩
  map_zero' := Subtype.ext (gaussianProfile_zero p l)
  map_add' c d := Subtype.ext (gaussianProfile_add p l c d)

theorem gaussianRayHom_bijective (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Bijective (gaussianRayHom p l) := by
  constructor
  · intro c d h
    have h' : gaussianProfile p l c = gaussianProfile p l d := congrArg Subtype.val h
    exact gaussianProfile_injective p hp l h'
  · rintro ⟨x, hx⟩
    rcases hx with ⟨c, rfl⟩
    exact ⟨c, rfl⟩

abbrev thetaRay := NNReal

def thetaRayGenerator : thetaRay := 1

def thetaToGaussian (p : Nat) (l : PrimeGeFive) : thetaRay →+ gaussianRay p l :=
  gaussianRayHom p l

theorem thetaToGaussian_bijective (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Bijective (thetaToGaussian p l) :=
  gaussianRayHom_bijective p hp l

/-! ## finite packet profile -/

variable (packet : FiniteThetaPacket l)

def packetProfile : ThetaLabel l → Real :=
  fun j => packet.scale (thetaToSigned l j)

theorem packetProfile_pos (j : ThetaLabel l) : 0 < packetProfile packet j :=
  packet.scale_pos _

theorem packetProfile_ne_zero (j : ThetaLabel l) : packetProfile packet j ≠ 0 :=
  (packetProfile_pos packet j).ne'

@[simp] theorem packetProfile_thetaZero :
    packetProfile packet (thetaZero l) = packet.q := by
  simp [packetProfile, thetaZero, thetaToSigned, packet.scale_eq, realThetaValue, gaussExponent]

@[simp] theorem packetProfile_thetaOne :
    packetProfile packet (thetaOne l) = packet.q ^ 4 := by
  simp [packetProfile, thetaOne, thetaToSigned, packet.scale_eq, realThetaValue, gaussExponent]

theorem packetProfile_ne_one (hq : packet.q ≠ 1) : packetProfile packet ≠ 1 := by
  intro h
  apply hq
  have h0 := congrFun h (thetaZero l)
  simpa [packetProfile_thetaZero] using h0

def packetGaussianCarrier : Set (ThetaLabel l → Real) :=
  {x | ∃ (u : ℝˣ) (n : Nat),
    x = (fun _ => (u : Real)) * packetProfile packet ^ n}

theorem packetGaussianCarrier_one : (1 : ThetaLabel l → Real) ∈ packetGaussianCarrier packet := by
  refine ⟨1, 0, ?_⟩
  funext j
  simp

theorem packetGaussianCarrier_mul {x y : ThetaLabel l → Real}
    (hx : x ∈ packetGaussianCarrier packet) (hy : y ∈ packetGaussianCarrier packet) :
    x * y ∈ packetGaussianCarrier packet := by
  rcases hx with ⟨u, m, rfl⟩
  rcases hy with ⟨v, n, rfl⟩
  refine ⟨u * v, m + n, ?_⟩
  funext j
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [pow_add]
  push_cast
  ring

def packetGaussianValueMonoid : Submonoid (ThetaLabel l → Real) where
  carrier := packetGaussianCarrier packet
  one_mem' := packetGaussianCarrier_one packet
  mul_mem' := packetGaussianCarrier_mul packet

theorem mem_packetGaussianValueMonoid_iff {x : ThetaLabel l → Real} :
    x ∈ packetGaussianValueMonoid packet ↔ ∃ (u : ℝˣ) (n : Nat),
      x = (fun _ => (u : Real)) * packetProfile packet ^ n := Iff.rfl

end Probe1966
