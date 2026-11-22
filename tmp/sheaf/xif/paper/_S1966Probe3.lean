import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open scoped BigOperators

namespace Probe1966

abbrev ThetaLabel (l : PrimeGeFive) := Fin (lStar l.value)

theorem one_lt_lStar (l : PrimeGeFive) : 1 < lStar l.value := by
  have h5 : 5 ≤ l.value := l.ge_five
  unfold lStar
  omega

def thetaZero (l : PrimeGeFive) : ThetaLabel l := ⟨0, by have := one_lt_lStar l; omega⟩
def thetaOne (l : PrimeGeFive) : ThetaLabel l := ⟨1, by exact one_lt_lStar l⟩

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

@[simp] theorem thetaToSigned_thetaZero (l : PrimeGeFive) :
    (thetaToSigned l (thetaZero l)).1 = 1 := rfl
@[simp] theorem thetaToSigned_thetaOne (l : PrimeGeFive) :
    (thetaToSigned l (thetaOne l)).1 = 2 := rfl

variable (packet : FiniteThetaPacket l)

def packetProfile : ThetaLabel l → Real :=
  fun j => packet.scale (thetaToSigned l j)

theorem packetProfile_pos (j : ThetaLabel l) : 0 < packetProfile packet j :=
  packet.scale_pos _

@[simp] theorem packetProfile_thetaZero :
    packetProfile packet (thetaZero l) = packet.q := by
  simp [packetProfile, thetaZero, thetaToSigned, packet.scale_eq, realThetaValue, gaussExponent]

@[simp] theorem packetProfile_thetaOne :
    packetProfile packet (thetaOne l) = packet.q ^ 4 := by
  simp [packetProfile, thetaOne, thetaToSigned, packet.scale_eq, realThetaValue, gaussExponent]

theorem packetProfile_pow_ne_diagonal (hq : packet.q ≠ 1) {k : Nat} (hk : 0 < k) :
    ¬ ∃ u : ℝˣ, packetProfile packet ^ k = fun _ => (u : Real) := by
  rintro ⟨u, hu⟩
  have h0 := congrFun hu (thetaZero l)
  have h1 := congrFun hu (thetaOne l)
  simp only [Pi.pow_apply, packetProfile_thetaZero, packetProfile_thetaOne] at h0 h1
  have hpow : packet.q ^ k = packet.q ^ (4 * k) := by
    calc
      packet.q ^ k = (packet.q ^ 4) ^ k := by rw [h0, h1]
      _ = packet.q ^ (4 * k) := by rw [pow_mul]
  have hk4 : k = 4 * k := pow_right_injective₀ packet.q_pos hq hpow
  omega

theorem packetGaussian_decomp_unique (hq : packet.q ≠ 1)
    {u v : ℝˣ} {m n : Nat}
    (h : (fun _ => (u : Real)) * packetProfile packet ^ m =
         (fun _ => (v : Real)) * packetProfile packet ^ n) :
    u = v ∧ m = n := by
  by_cases hmn : m = n
  · subst n
    constructor
    · apply Units.ext
      have h0 := congrFun h (thetaZero l)
      simp only [Pi.mul_apply, Pi.pow_apply, packetProfile_thetaZero] at h0
      exact mul_right_cancel₀ (pow_ne_zero m packet.q_pos.ne') h0
    · rfl
  · exfalso
    have h0 := congrFun h (thetaZero l)
    have h1 := congrFun h (thetaOne l)
    simp only [Pi.mul_apply, Pi.pow_apply, packetProfile_thetaZero, packetProfile_thetaOne] at h0 h1
    have hA : (u : Real) * packet.q ^ m * (packet.q ^ 4) ^ n =
        (v : Real) * packet.q ^ n * (packet.q ^ 4) ^ n := by rw [h0]
    have hB : (u : Real) * (packet.q ^ 4) ^ m * packet.q ^ n =
        (v : Real) * (packet.q ^ 4) ^ n * packet.q ^ n := by rw [h1]
    have hR : (v : Real) * packet.q ^ n * (packet.q ^ 4) ^ n =
        (v : Real) * (packet.q ^ 4) ^ n * packet.q ^ n := by ring
    have hL : (u : Real) * packet.q ^ m * (packet.q ^ 4) ^ n =
        (u : Real) * (packet.q ^ 4) ^ m * packet.q ^ n := by
      rw [hA, hR, ← hB]
    have hu : (u : Real) ≠ 0 := by exact_mod_cast u.ne_zero
    have hq' : packet.q ^ m * (packet.q ^ 4) ^ n =
        (packet.q ^ 4) ^ m * packet.q ^ n := by
      apply mul_left_cancel₀ hu
      simpa [mul_assoc] using hL
    have hpow : packet.q ^ (m + 4 * n) = packet.q ^ (n + 4 * m) := by
      calc
        packet.q ^ (m + 4 * n) = packet.q ^ m * packet.q ^ (4 * n) := by rw [pow_add]
        _ = packet.q ^ m * (packet.q ^ 4) ^ n := by rw [pow_mul]
        _ = (packet.q ^ 4) ^ m * packet.q ^ n := hq'
        _ = packet.q ^ (4 * m) * packet.q ^ n := by rw [pow_mul]
        _ = packet.q ^ (4 * m + n) := by rw [pow_add]
        _ = packet.q ^ (n + 4 * m) := by congr 1; omega
    have hmn' : m + 4 * n = n + 4 * m := pow_right_injective₀ packet.q_pos hq hpow
    omega

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

theorem mem_packetGaussianCarrier_iff {x : ThetaLabel l → Real} :
    x ∈ packetGaussianCarrier packet ↔ ∃ (u : ℝˣ) (n : Nat),
      x = (fun _ => (u : Real)) * packetProfile packet ^ n := Iff.rfl

def packetGaussianValueMonoid : Submonoid (ThetaLabel l → Real) where
  carrier := packetGaussianCarrier packet
  one_mem' := packetGaussianCarrier_one packet
  mul_mem' := packetGaussianCarrier_mul packet

abbrev PacketThetaMonoid := ℝˣ × Multiplicative Nat

def packetThetaGenerator : PacketThetaMonoid := (1, Multiplicative.ofAdd 1)

def packetEvaluation : PacketThetaMonoid →* packetGaussianValueMonoid packet where
  toFun z :=
    ⟨(fun _ => (z.1 : Real)) * packetProfile packet ^ Multiplicative.toAdd z.2, by
      show (fun _ => (z.1 : Real)) * packetProfile packet ^ Multiplicative.toAdd z.2 ∈
          packetGaussianCarrier packet
      rw [mem_packetGaussianCarrier_iff]
      exact ⟨z.1, Multiplicative.toAdd z.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    funext j
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    funext j
    change ((a.1 * b.1 : ℝˣ) : Real) *
        packetProfile packet j ^ (Multiplicative.toAdd (a.2 * b.2)) =
      ((a.1 : Real) * packetProfile packet j ^ Multiplicative.toAdd a.2) *
        ((b.1 : Real) * packetProfile packet j ^ Multiplicative.toAdd b.2)
    rw [Units.val_mul, toAdd_mul, pow_add]
    ring

theorem packetEvaluation_injective (hq : packet.q ≠ 1) :
    Function.Injective (packetEvaluation packet) := by
  rintro ⟨u, m⟩ ⟨v, n⟩ h
  have hval : (fun _ => (u : Real)) * packetProfile packet ^ (Multiplicative.toAdd m) =
      (fun _ => (v : Real)) * packetProfile packet ^ (Multiplicative.toAdd n) := by
    exact congrArg Subtype.val h
  obtain ⟨huv, hmn⟩ := packetGaussian_decomp_unique packet hq hval
  exact Prod.ext huv (Multiplicative.toAdd.injective hmn)

end Probe1966
