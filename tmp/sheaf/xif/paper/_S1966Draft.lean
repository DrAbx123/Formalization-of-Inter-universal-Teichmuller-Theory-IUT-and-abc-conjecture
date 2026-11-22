import Iut.Foundations.SourceDefinition52LocalReconstruction
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open Iut.SourceFinitePlaceReconstruction
open scoped BigOperators

/-!
# S1966: the local theta / Gaussian monoid, actually constructed where the tree allows it

Layer: O (original Theta-link / q-pilot), the first object of IUT II,
Corollary 4.6, (iv), on the source places.

The paper's first object is the local theta-monoid assignment

  PsiFenv(daggerHT_Theta) = { Psi_{daggerF_Theta,v} }_{v in V}

of IUT II, Corollary 4.6, (iv).  At a good nonarchimedean place its local
construction is IUT II, Proposition 4.1, (i)--(iv):

  Psi_cns(Pi_v)            ind-topological constant monoid, isomorphic to O^tri,
  Psi_cns(Pi_v)^x         its units,
  Psi_env(Pi_v)  = Psi_cns(Pi_v)^x x { R>=0 * log(p_v) * log(Theta) },
  Psi_gau(Pi_v)  = Psi_cns(Pi_v)^x<F_l^*> x { R>=0 * (..., j^2 log(p_v), ...) }

inside the product of the semi-simplified constant monoids
Psi_ss_cns(Pi_v) = Psi_cns(Pi_v)^x x R>=0, together with the formal evaluation
isomorphism sending log(p_v) log(Theta) to (..., j^2 log(p_v), ...).

## What is constructed here (all kernel-checked)

1. The Gaussian ray 'gaussianRay p l': the genuine submonoid
   { c * (j |-> (j+1)^2 * log p) | c : R>=0 } of (ThetaLabel l -> R),
   with an additive equivalence to R>=0.  This is exactly the non-unit
   Gaussian factor of Proposition 4.1, (iv).

2. The formal log direction and its evaluation 'thetaRay' / 'thetaToGaussian':
   the coefficient monoid R>=0 * log(p_v) * log(Theta) (with the formal
   symbol represented by the coefficient 1) and the evaluation
   c |-> c * (j |-> (j+1)^2 * log p).  It is bijective onto the Gaussian
   ray.  This is the paper's formal evaluation on the non-unit factors.

3. The finite theta-packet Gaussian value monoid
   'packetGaussianValueMonoid packet':
   from the finite theta packet q, scale j = q^(j^2), the submonoid
   (R^x)<F_l^*> * xi^N of (ThetaLabel l -> R), where
   xi j = packet.scale (j+1).  This is the finite real value-profile shadow
   of Corollary 3.5, (ii)/3.6, (ii): units times the N-th powers of the value
   profile.  The map R^x x N -> packetGaussianValueMonoid is a monoid
   isomorphism onto its image, and is injective whenever packet.q != 1.
   In particular it applies to the actual source Gaussian five packet
   'gaussianFivePacket' (q = 1/5); 'C3GaussianThetaPacketActual' proves that
   the source theater's packet is FiniteThetaPacket.ofQ (1/5), which this
   definition formalizes.

4. The actual-local semi-simplified monoid
   'LocalThetaMonoidModel v' and 'LocalGaussianMonoidModel v p l':
   using the actual local units (IndIntegralMonoid (QPlace v))^x (the
   ind-topological integral monoid of IUT I, Definition 5.2, (v), reconstructed
   in 'Iut/Foundations/SourceDefinition52LocalReconstruction.lean') and the
   exact Gaussian ray j |-> (j+1)^2 * log p, the file constructs the
   submonoid

     (units)<F_l^*> * { c * (..., j^2 log(p_v), ...) }

   of the product of the semi-simplified monoids
   units x Multiplicative R>=0, together with the evaluation

     (u, c) |-> diag(u) * (j |-> c * (j+1)^2 * log p),

   which is bijective onto the constructed Gaussian monoid.  This is a genuine
   local theta/Gaussian monoid on the actual local-field model, not a carrier
   record and not an arbitrary one-point monoid.  The tree's existing
   'SourceLGPMonoidLayer.LGPMonoid' is a finite LGP splitting monoid generated
   by real theta values at q=2; it is not the paper's theta/Gaussian monoid,
   and it is not identified with the monoids constructed here.

## Exact first missing

The paper's Psi_cns(Pi_v) is constructed by the group-theoretic algorithm of
[AbsTopIII], Corollary 1.10, (b), from the topological group Pi_v (IUT II,
Proposition 4.1, (i)); it is an ind-topological submonoid of
lim H^1(J, mu_hat^Z(G_v)), isomorphic to O^tri_{F_v}.  The tree has no such
group-theoretic constant-monoid construction from Pi_v, and no G_v(Pi_v)-action
on such a Psi_cns.  It does have the actual local integral monoid
IndIntegralMonoid (with its ind-topology and Krull action) and
SourceLogShellDatum.Units; those are actual local-field models of O^tri, but no
identification of either with Psi_cns(Pi_v) or its units is constructed.
Hence:

* the first missing object is Psi_cns(Pi_v) together with its G_v(Pi_v)-action,
  i.e. the algorithm of Proposition 4.1, (i);
* consequently the paper's Psi_env(Pi_v) and Psi_gau(Pi_v) (with the diagonal
  <F_l^*> units) are not defined here; the monoids below use the actual local
  units as an explicit model and are named ...Model;
* the G_v(Pi_v)-actions and splittings required in Proposition 4.1, (iv), are
  also not constructed;
* at bad v, the Frobenioid-theoretic theta function Theta_v and the theta
  monoid Psi_{daggerF_Theta,v} of Corollary 3.6, (ii), are missing; the finite
  theta packet is real-valued and cannot supply an element of O^x(T^div);
* the assignment over all v and the Theta-bridge gluing of Corollary 4.6, (iv),
  are not constructed.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only Nonempty gate is used.  The missing objects are named as
missing, not replaced by a fake monoid.
-/

namespace LeanFormal.IUT.XiFPaper.S1966LocalThetaMonoidActual

/-! ## 1. The label index 1 <= j <= l^* and the Gaussian weights -/

/-- The paper's positive label index 1 <= j <= l^*, represented by
Fin (lStar l.value). -/
abbrev ThetaLabel (l : PrimeGeFive) := Fin (lStar l.value)

theorem one_lt_lStar (l : PrimeGeFive) : 1 < lStar l.value := by
  have h5 : 5 <= l.value := l.ge_five
  unfold lStar
  omega

/-- The label j = 1. -/
def thetaZero (l : PrimeGeFive) : ThetaLabel l :=
  ⟨0, by have := one_lt_lStar l; omega⟩

/-- The label j = 2. -/
def thetaOne (l : PrimeGeFive) : ThetaLabel l :=
  ⟨1, by exact one_lt_lStar l⟩

/-- The embedding of the positive labels into the signed labels used by the
finite theta packet.  The positive label j : Fin (l^*) is the signed label
j+1. -/
def thetaToSigned (l : PrimeGeFive) (j : ThetaLabel l) : SignedLabel l.value :=
  ⟨(j.1 : Int) + 1, by
    have hj : j.1 < lStar l.value := j.2
    have hj0 : (0 : Int) <= (j.1 : Int) := by exact_mod_cast Nat.zero_le j.1
    have hk : (1 : Int) <= (lStar l.value : Int) := by
      exact_mod_cast le_of_lt (one_lt_lStar l)
    constructor
    · omega
    · have hle : j.1 + 1 <= lStar l.value := Nat.succ_le_of_lt hj
      exact_mod_cast hle⟩

@[simp] theorem thetaToSigned_thetaZero (l : PrimeGeFive) :
    (thetaToSigned l (thetaZero l)).1 = 1 := rfl

@[simp] theorem thetaToSigned_thetaOne (l : PrimeGeFive) :
    (thetaToSigned l (thetaOne l)).1 = 2 := rfl

/-- The Gaussian weight j^2 * log(p_v) of IUT II, Proposition 4.1, (iv),
with j = i+1 for i : ThetaLabel l. -/
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

/-- The nonnegative Gaussian weight as an NNReal. -/
def gaussianNNWeight (p : Nat) (l : PrimeGeFive) : ThetaLabel l → NNReal :=
  fun j => Real.toNNReal (gaussianWeight p l j)

theorem coe_gaussianNNWeight (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive)
    (j : ThetaLabel l) :
    (gaussianNNWeight p l j : Real) = gaussianWeight p l j :=
  Real.coe_toNNReal _ (le_of_lt (gaussianWeight_pos p hp l j))

theorem gaussianNNWeight_thetaZero (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    gaussianNNWeight p l (thetaZero l) ≠ 0 := by
  intro h
  have hcoe : (gaussianNNWeight p l (thetaZero l) : Real) = 0 := by rw [h]; simp
  rw [coe_gaussianNNWeight p hp l (thetaZero l)] at hcoe
  have hpos := gaussianWeight_pos p hp l (thetaZero l)
  linarith

/-! ## 2. The Gaussian ray and the formal log direction -/

/-- The scalar multiple c * (j |-> j^2 log p). -/
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

/-- The Gaussian ray { R>=0 * (..., j^2 log(p_v), ...) } of IUT II,
Proposition 4.1, (iv), as an additive submonoid of the product monoid. -/
def gaussianRay (p : Nat) (l : PrimeGeFive) :
    AddSubmonoid (ThetaLabel l → Real) where
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

/-- The additive monoid R>=0 of coefficients, embedded as the Gaussian ray. -/
def gaussianRayHom (p : Nat) (l : PrimeGeFive) :
    NNReal →+ gaussianRay p l where
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

/-- The formal theta direction R>=0 * log(p_v) * log(Theta); the formal
symbol is represented by the coefficient 1. -/
abbrev thetaRay := NNReal

def thetaRayGenerator : thetaRay := 1

/-- The formal evaluation log(p_v) log(Theta) |-> (..., j^2 log(p_v), ...)
of IUT II, Proposition 4.1, (iv), on the non-unit factors. -/
def thetaToGaussian (p : Nat) (l : PrimeGeFive) : thetaRay →+ gaussianRay p l :=
  gaussianRayHom p l

theorem thetaToGaussian_bijective (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Bijective (thetaToGaussian p l) :=
  gaussianRayHom_bijective p hp l

/-! ## 3. The finite theta-packet Gaussian value monoid -/

variable (packet : FiniteThetaPacket l)

/-- The real value profile xi j = scale(j+1) = q^((j+1)^2) of the finite
theta packet. -/
def packetProfile : ThetaLabel l → Real :=
  fun j => packet.scale (thetaToSigned l j)

theorem packetProfile_pos (j : ThetaLabel l) : 0 < packetProfile packet j :=
  packet.scale_pos _

theorem packetProfile_ne_zero (j : ThetaLabel l) : packetProfile packet j ≠ 0 :=
  (packetProfile_pos packet j).ne'

@[simp] theorem packetProfile_thetaZero :
    packetProfile packet (thetaZero l) = packet.q := by
  simp [packetProfile, thetaZero, thetaToSigned, packet.scale_eq,
    realThetaValue, gaussExponent]

@[simp] theorem packetProfile_thetaOne :
    packetProfile packet (thetaOne l) = packet.q ^ 4 := by
  simp [packetProfile, thetaOne, thetaToSigned, packet.scale_eq,
    realThetaValue, gaussExponent]

/-- The finite Gaussian carrier (R^x)<F_l^*> * xi^N of Corollary 3.5,
(ii)/3.6, (ii), with the real value profile xi. -/
def packetGaussianCarrier : Set (ThetaLabel l → Real) :=
  {x | ∃ (u : ℝˣ) (n : Nat),
    x = (fun _ => (u : Real)) * packetProfile packet ^ n}

theorem packetGaussianCarrier_one :
    (1 : ThetaLabel l → Real) ∈ packetGaussianCarrier packet := by
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

/-- The finite Gaussian value monoid (R^x)<F_l^*> * xi^N. -/
def packetGaussianValueMonoid : Submonoid (ThetaLabel l → Real) where
  carrier := packetGaussianCarrier packet
  one_mem' := packetGaussianCarrier_one packet
  mul_mem' := packetGaussianCarrier_mul packet

theorem mem_packetGaussianCarrier_iff {x : ThetaLabel l → Real} :
    x ∈ packetGaussianCarrier packet ↔ ∃ (u : ℝˣ) (n : Nat),
      x = (fun _ => (u : Real)) * packetProfile packet ^ n := Iff.rfl

theorem packetProfile_mem :
    packetProfile packet ∈ packetGaussianValueMonoid packet := by
  refine ⟨1, 1, ?_⟩
  funext j
  simp

theorem packetDiagonal_mem (u : ℝˣ) :
    (fun _ => (u : Real)) ∈ packetGaussianValueMonoid packet := by
  refine ⟨u, 0, ?_⟩
  funext j
  simp

/-- The finite theta monoid model R^x x N: units times the N-powers of the
formal theta generator. -/
abbrev PacketThetaMonoid := ℝˣ × Multiplicative Nat

def packetThetaGenerator : PacketThetaMonoid := (1, Multiplicative.ofAdd 1)

/-- The finite evaluation (u,n) |-> diag(u) * xi^n. -/
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

/-- The finite evaluation at the formal generator is the value profile. -/
@[simp] theorem packetEvaluation_generator :
    packetEvaluation packet packetThetaGenerator =
      ⟨packetProfile packet, ⟨1, 1, by funext j; simp⟩⟩ := by
  apply Subtype.ext
  funext j
  simp [packetThetaGenerator, packetEvaluation]

/-- The finite evaluation is the identity on the unit factor. -/
@[simp] theorem packetEvaluation_units (u : ℝˣ) :
    packetEvaluation packet (u, 1) =
      ⟨fun _ => (u : Real), ⟨u, 0, by funext j; simp⟩⟩ := by
  apply Subtype.ext
  funext j
  simp [packetEvaluation]

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
    simp only [Pi.mul_apply, Pi.pow_apply, packetProfile_thetaZero,
      packetProfile_thetaOne] at h0 h1
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

theorem packetEvaluation_injective (hq : packet.q ≠ 1) :
    Function.Injective (packetEvaluation packet) := by
  rintro ⟨u, m⟩ ⟨v, n⟩ h
  have hval : (fun _ => (u : Real)) * packetProfile packet ^ (Multiplicative.toAdd m) =
      (fun _ => (v : Real)) * packetProfile packet ^ (Multiplicative.toAdd n) := by
    exact congrArg Subtype.val h
  obtain ⟨huv, hmn⟩ := packetGaussian_decomp_unique packet hq hval
  exact Prod.ext huv (Multiplicative.toAdd.injective hmn)

theorem packetEvaluation_bijective (hq : packet.q ≠ 1) :
    Function.Bijective (packetEvaluation packet) := by
  refine ⟨packetEvaluation_injective packet hq, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨u, n, rfl⟩
  exact ⟨(u, Multiplicative.ofAdd n), rfl⟩

/-- The actual source Gaussian five packet q = 1/5.  It is the packet
identified with the source theater packet in C3GaussianThetaPacketActual. -/
def gaussianFivePacket (l : PrimeGeFive) : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (l := l) ((5 : Real)⁻¹) (by norm_num)

@[simp] theorem gaussianFivePacket_q :
    (gaussianFivePacket l).q = (5 : Real)⁻¹ := rfl

theorem gaussianFivePacket_q_ne_one : (gaussianFivePacket l).q ≠ 1 := by
  rw [gaussianFivePacket_q]
  norm_num

theorem gaussianFivePacket_evaluation_injective :
    Function.Injective (packetEvaluation (gaussianFivePacket l)) :=
  packetEvaluation_injective _ gaussianFivePacket_q_ne_one

/-! ## 4. The actual-local semi-simplified monoid -/

/-- The actual local units used as a model of Psi_cns(Pi_v)^x: the units of
the ind-topological integral monoid of IUT I, Definition 5.2, (v),
reconstructed from the actual local field. -/
abbrev ActualLocalUnits (v : FinitePrimePlace 2 7) : Type :=
  (IndIntegralMonoid (finitePrimePlaceToQ v))ˣ

/-- The paper's semi-simplified monoid Psi_ss = Psi_cns^x x R>=0, on the
actual local units model.  The second factor is R>=0 in multiplicative
notation, i.e. Multiplicative R>=0 with multiplication = addition. -/
abbrev LocalSemiSimplified (v : FinitePrimePlace 2 7) : Type :=
  ActualLocalUnits v × Multiplicative NNReal

/-- The local theta monoid of Proposition 4.1, (iv), on the actual local
units model: units times the formal R>=0 * log(p_v) * log(Theta)
direction. -/
abbrev LocalThetaMonoidModel (v : FinitePrimePlace 2 7) : Type :=
  ActualLocalUnits v × Multiplicative NNReal

/-- The Gaussian carrier units<F_l^*> * {c (..., j^2 log p, ...)} inside the
product of the semi-simplified monoids. -/
def localGaussianCarrier (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive) :
    Set (ThetaLabel l → LocalSemiSimplified v) :=
  {x | ∃ (u : ActualLocalUnits v) (c : NNReal),
    x = fun j => (u, Multiplicative.ofAdd (c * gaussianNNWeight p l j))}

theorem localDiagonal_mem (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive)
    (u : ActualLocalUnits v) :
    (fun _ : ThetaLabel l => (u, 1)) ∈ localGaussianCarrier v p l := by
  refine ⟨u, 0, ?_⟩
  funext j
  rw [zero_mul, ofAdd_zero]

theorem localGaussian_mem (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive)
    (c : NNReal) :
    (fun j => (1, Multiplicative.ofAdd (c * gaussianNNWeight p l j))) ∈
      localGaussianCarrier v p l :=
  ⟨1, c, rfl⟩

theorem localGaussianCarrier_one (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive) :
    (1 : ThetaLabel l → LocalSemiSimplified v) ∈ localGaussianCarrier v p l := by
  refine ⟨1, 0, ?_⟩
  funext j
  rw [Pi.one_apply]
  apply Prod.ext
  · rfl
  · rw [zero_mul, ofAdd_zero]
    rfl

theorem localGaussianCarrier_mul (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive)
    {x y : ThetaLabel l → LocalSemiSimplified v}
    (hx : x ∈ localGaussianCarrier v p l) (hy : y ∈ localGaussianCarrier v p l) :
    x * y ∈ localGaussianCarrier v p l := by
  rcases hx with ⟨u, c, rfl⟩
  rcases hy with ⟨w, d, rfl⟩
  refine ⟨u * w, c + d, ?_⟩
  funext j
  simp only [Pi.mul_apply, Prod.mul_def]
  apply Prod.ext
  · rfl
  · rw [← ofAdd_add]
    congr 1
    rw [add_mul]

/-- The local Gaussian monoid of Proposition 4.1, (iv), on the actual local
units model. -/
def localGaussianValueMonoid (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive) :
    Submonoid (ThetaLabel l → LocalSemiSimplified v) where
  carrier := localGaussianCarrier v p l
  one_mem' := localGaussianCarrier_one v p l
  mul_mem' := localGaussianCarrier_mul v p l

theorem mem_localGaussianCarrier_iff (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive)
    {x : ThetaLabel l → LocalSemiSimplified v} :
    x ∈ localGaussianCarrier v p l ↔ ∃ (u : ActualLocalUnits v) (c : NNReal),
      x = fun j => (u, Multiplicative.ofAdd (c * gaussianNNWeight p l j)) := Iff.rfl

/-- The formal generator log(p_v) log(Theta), represented by the coefficient 1. -/
def localThetaGenerator (v : FinitePrimePlace 2 7) : LocalThetaMonoidModel v :=
  (1, Multiplicative.ofAdd 1)

/-- The evaluation (u,c) |-> diag(u) * c (..., j^2 log p, ...) of IUT II,
Proposition 4.1, (iv), on the actual local units model. -/
def localEvaluation (v : FinitePrimePlace 2 7) (p : Nat) (l : PrimeGeFive) :
    LocalThetaMonoidModel v →* localGaussianValueMonoid v p l where
  toFun z :=
    ⟨fun j => (z.1, Multiplicative.ofAdd (z.2.toAdd * gaussianNNWeight p l j)), by
      show (fun j => (z.1, Multiplicative.ofAdd (z.2.toAdd * gaussianNNWeight p l j))) ∈
        localGaussianCarrier v p l
      rw [mem_localGaussianCarrier_iff]
      exact ⟨z.1, z.2.toAdd, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    funext j
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    funext j
    change (a.1 * b.1, Multiplicative.ofAdd ((a.2 * b.2).toAdd * gaussianNNWeight p l j)) =
      (a.1, Multiplicative.ofAdd (a.2.toAdd * gaussianNNWeight p l j)) *
      (b.1, Multiplicative.ofAdd (b.2.toAdd * gaussianNNWeight p l j))
    simp only [Prod.mul_def]
    apply Prod.ext
    · rfl
    · rw [toAdd_mul, add_mul, ofAdd_add]

/-- The evaluation is the identity on the unit factor. -/
@[simp] theorem localEvaluation_units (v : FinitePrimePlace 2 7) (p : Nat)
    (l : PrimeGeFive) (u : ActualLocalUnits v) :
    localEvaluation v p l (u, 1) =
      ⟨fun _ => (u, 1), ⟨u, 0, by funext j; rw [zero_mul, ofAdd_zero]⟩⟩ := by
  apply Subtype.ext
  funext j
  simp [localEvaluation]

/-- The evaluation sends the formal generator to the Gaussian vector
(..., j^2 log(p_v), ...). -/
@[simp] theorem localEvaluation_generator (v : FinitePrimePlace 2 7) (p : Nat)
    (l : PrimeGeFive) :
    localEvaluation v p l (localThetaGenerator v) =
      ⟨fun j => (1, Multiplicative.ofAdd (gaussianNNWeight p l j)),
        ⟨1, 1, by funext j; simp⟩⟩ := by
  apply Subtype.ext
  funext j
  simp [localEvaluation, localThetaGenerator]

theorem localEvaluation_injective (v : FinitePrimePlace 2 7) (p : Nat)
    (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Injective (localEvaluation v p l) := by
  rintro ⟨u, c⟩ ⟨w, d⟩ h
  have hval : (localEvaluation v p l (u, c) : ThetaLabel l → LocalSemiSimplified v) =
      localEvaluation v p l (w, d) := congrArg Subtype.val h
  have h0 := congrFun hval (thetaZero l)
  change (u, Multiplicative.ofAdd (c.toAdd * gaussianNNWeight p l (thetaZero l))) =
      (w, Multiplicative.ofAdd (d.toAdd * gaussianNNWeight p l (thetaZero l))) at h0
  have huw : u = w := congrArg Prod.fst h0
  have hcd : c.toAdd * gaussianNNWeight p l (thetaZero l) =
      d.toAdd * gaussianNNWeight p l (thetaZero l) := congrArg Prod.snd h0
  have hcdeq : c.toAdd = d.toAdd :=
    mul_right_cancel₀ (gaussianNNWeight_thetaZero p hp l) hcd
  have hcd' : c = d := Multiplicative.toAdd.injective hcdeq
  exact Prod.ext huw hcd'

theorem localEvaluation_bijective (v : FinitePrimePlace 2 7) (p : Nat)
    (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Bijective (localEvaluation v p l) := by
  refine ⟨localEvaluation_injective v p hp l, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨u, c, rfl⟩
  exact ⟨(u, Multiplicative.ofAdd c), rfl⟩

/-! ## 5. Consumer: every Hodge theater's finite theta packet -/

section HodgeTheaterConsumer

variable {V : Type} (HT : HodgeTheater l V)

/-- The finite Gaussian value monoid of an arbitrary Hodge theater's theta
packet.  This is the tree's finite HodgeTheater packet, not the paper's
F-prime-strip / local theta monoid. -/
def hodgePacketGaussianValueMonoid : Submonoid (ThetaLabel l → Real) :=
  packetGaussianValueMonoid HT.thetaPacket

theorem hodgePacketGaussianValueMonoid_thetaZero :
    packetProfile HT.thetaPacket (thetaZero l) = HT.thetaPacket.q :=
  packetProfile_thetaZero HT.thetaPacket

end HodgeTheaterConsumer

/-! ## 6. Axiom probes -/

#print axioms thetaToGaussian_bijective
#print axioms packetEvaluation_injective
#print axioms localEvaluation_injective

end LeanFormal.IUT.XiFPaper.S1966LocalThetaMonoidActual


