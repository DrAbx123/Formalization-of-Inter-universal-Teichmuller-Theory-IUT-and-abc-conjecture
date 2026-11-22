import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeries
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# The logarithm on the actual full integral unit group

For IUT III Definition 1.1 and Remark 1.2.2(i), construct the logarithm
on the full valuation-integer unit group, rather than postulating a map.
The finite principal-unit quotient supplies a uniform positive exponent.
Dividing the principal logarithm of that power is independent of the
exponent, continuous, and multiplicative-to-additive.

This file constructs the actual compact image and its scaled log-shell.
The inclusion of the integer ring in that shell requires the local inverse
theorem, proved separately; it is not an assumption of this construction.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

/-- The analytic logarithm law on actual principal integral units. -/
theorem principalUnitLog_mul (u v : (Integers K)ˣ)
    (hu : u ∈ principalUnits) (hv : v ∈ principalUnits) :
    log1p (((u * v).val : K) - 1) =
      log1p ((u.val : K) - 1) + log1p ((v.val : K) - 1) := by
  have heq : (((u * v).val : K) - 1) =
      ((u.val : K) - 1) + ((v.val : K) - 1) +
        ((u.val : K) - 1) * ((v.val : K) - 1) := by
    simp only [Units.val_mul, Subring.coe_mul]
    ring
  rw [heq]
  exact log1p_add_mul (p := p) _ _ hu hv

/-- On principal units the logarithm of a power is the integer multiple. -/
theorem principalUnitLog_pow (u : (Integers K)ˣ)
    (hu : u ∈ principalUnits) (n : ℕ) :
    log1p (((u ^ n).val : K) - 1) = (n : K) * log1p ((u.val : K) - 1) := by
  induction n with
  | zero => simp [log1p_zero]
  | succ n ih =>
    rw [pow_succ, principalUnitLog_mul (p := p) _ _
      ((principalUnits (K := K)).pow_mem hu n) hu, ih]
    push_cast
    ring

omit localNormedAlgebra in
/-- The candidate obtained using an exponent that lands in principal units.
Its definition is analytic; the exponent condition is needed for its laws. -/
def unitLogWithExponent (n : ℕ) (u : (Integers K)ˣ) : K :=
  log1p (((u ^ n).val : K) - 1) / (n : K)

/-- Any two positive exponents that reach principal units give the same
value. Thus the extension is independent of the finite-quotient choice. -/
theorem unitLogWithExponent_independent (u : (Integers K)ˣ)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hun : u ^ n ∈ principalUnits) (hum : u ^ m ∈ principalUnits) :
    unitLogWithExponent n u = unitLogWithExponent m u := by
  have hcomm : (u ^ n) ^ m = (u ^ m) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hcross : (m : K) * log1p (((u ^ n).val : K) - 1) =
      (n : K) * log1p (((u ^ m).val : K) - 1) := by
    rw [← principalUnitLog_pow (p := p) _ hun m,
      ← principalUnitLog_pow (p := p) _ hum n, hcomm]
  unfold unitLogWithExponent
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hm)).mpr
  simpa only [mul_comm] using hcross

/-- Any uniform principal-unit exponent gives a continuous map on all units. -/
theorem continuous_unitLogWithExponent (n : ℕ)
    (hn : ∀ u : (Integers K)ˣ, u ^ n ∈ principalUnits) :
    Continuous (unitLogWithExponent (K := K) n) := by
  have hc : Continuous (fun u : (Integers K)ˣ => ((u ^ n).val : K) - 1) := by
    have hval : Continuous (fun u : (Integers K)ˣ => (u.val : K)) :=
      continuous_subtype_val.comp Units.continuous_val
    have hpow : Continuous (fun u : (Integers K)ˣ => (u.val : K) ^ n - 1) :=
      (hval.pow n).sub continuous_const
    simpa only [Units.val_pow_eq_pow_val, Subring.coe_pow] using
      hpow
  have hlog : Continuous (fun u : (Integers K)ˣ =>
      log1p (((u ^ n).val : K) - 1)) :=
    (log1p_continuousOn_ball (p := p)).comp_continuous hc (fun u => by
      simpa only [Metric.mem_ball, dist_zero_right] using
        ((mem_principalUnits_iff _).mp (hn u)))
  exact hlog.div_const _

variable [ProperSpace K]

omit localNormedAlgebra in
/-- A uniform exponent constructed from the actual finite unit quotient: the
cardinality of the principal-unit quotient. -/
def integralUnitExponent : ℕ :=
  Nat.card ((Integers K)ˣ ⧸ principalUnits (K := K))

omit localNormedAlgebra [CharZero K] [CompleteSpace K] in
theorem integralUnitExponent_pos : 0 < integralUnitExponent (K := K) := by
  letI : Finite ((Integers K)ˣ ⧸ principalUnits (K := K)) :=
    finite_principalUnitQuotient (K := K)
  haveI : Nonempty ((Integers K)ˣ ⧸ principalUnits (K := K)) :=
    ⟨QuotientGroup.mk 1⟩
  unfold integralUnitExponent
  exact Nat.card_pos

omit localNormedAlgebra [CharZero K] [CompleteSpace K] in
theorem pow_integralUnitExponent_mem (u : (Integers K)ˣ) :
    u ^ integralUnitExponent (K := K) ∈ principalUnits := by
  letI : Finite ((Integers K)ˣ ⧸ principalUnits (K := K)) :=
    finite_principalUnitQuotient (K := K)
  letI := Fintype.ofFinite ((Integers K)ˣ ⧸ principalUnits (K := K))
  have hcard : Fintype.card ((Integers K)ˣ ⧸ principalUnits (K := K)) =
      integralUnitExponent (K := K) := by
    unfold integralUnitExponent
    exact (Nat.card_eq_fintype_card).symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one

omit localNormedAlgebra in
/-- The actual logarithm of an arbitrary integral unit. -/
def unitLog (u : (Integers K)ˣ) : K :=
  unitLogWithExponent (integralUnitExponent (K := K)) u

/-- The constructed logarithm can be evaluated using any positive exponent
for this particular unit, without a uniform-exponent hypothesis. -/
theorem unitLog_eq_withExponent (u : (Integers K)ˣ) {n : ℕ}
    (hn : n ≠ 0) (hun : u ^ n ∈ principalUnits) :
    unitLog u = unitLogWithExponent n u :=
  unitLogWithExponent_independent (p := p) u
    (ne_of_gt integralUnitExponent_pos) hn (pow_integralUnitExponent_mem u) hun

/-- The extension agrees with the analytic series on every principal unit. -/
theorem unitLog_eq_log1p (u : (Integers K)ˣ) (hu : u ∈ principalUnits) :
    unitLog u = log1p ((u.val : K) - 1) := by
  rw [unitLog_eq_withExponent (p := p) u (n := 1) one_ne_zero (by simpa using hu)]
  simp [unitLogWithExponent]

theorem unitLog_one : unitLog (1 : (Integers K)ˣ) = 0 := by
  rw [unitLog_eq_log1p (p := p) _ (principalUnits.one_mem)]
  simp [log1p_zero]

/-- Multiplicativity of actual units becomes additivity in the local field. -/
theorem unitLog_mul (u v : (Integers K)ˣ) :
    unitLog (u * v) = unitLog u + unitLog v := by
  let n := integralUnitExponent (K := K)
  change unitLogWithExponent n (u * v) =
    unitLogWithExponent n u + unitLogWithExponent n v
  simp only [unitLogWithExponent, mul_pow]
  rw [principalUnitLog_mul (p := p) _ _ (pow_integralUnitExponent_mem u)
    (pow_integralUnitExponent_mem v), add_div]

theorem unitLog_pow (u : (Integers K)ˣ) (n : ℕ) :
    unitLog (u ^ n) = (n : K) * unitLog u := by
  induction n with
  | zero => simp [unitLog_one (p := p)]
  | succ n ih =>
    rw [pow_succ, unitLog_mul (p := p), ih]
    push_cast
    ring

theorem unitLog_inv (u : (Integers K)ˣ) : unitLog u⁻¹ = -unitLog u := by
  have h := unitLog_mul (p := p) u u⁻¹
  rw [mul_inv_cancel, unitLog_one (p := p)] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem continuous_unitLog : Continuous (unitLog (K := K)) :=
  continuous_unitLogWithExponent (p := p) _ pow_integralUnitExponent_mem

/-- Bundled version of the constructed logarithm, with all laws proved. -/
def unitLogHom : (Integers K)ˣ →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (unitLog u)
  map_one' := by change unitLog (1 : (Integers K)ˣ) = 0; exact unitLog_one (p := p)
  map_mul' u v := by change unitLog (u * v) = unitLog u + unitLog v; exact unitLog_mul (p := p) u v

/-- Agreement on the actual principal-unit subgroup determines the full
logarithm uniquely; there is no unspecified choice in the extension. -/
theorem unitLogHom_unique (f : (Integers K)ˣ →* Multiplicative K)
    (hf : ∀ u : (Integers K)ˣ, u ∈ principalUnits →
      Multiplicative.toAdd (f u) = log1p ((u.val : K) - 1)) :
    f = unitLogHom (p := p) := by
  ext u
  change Multiplicative.toAdd (f u) = unitLog u
  let n := integralUnitExponent (K := K)
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt integralUnitExponent_pos)
  have hpower := hf (u ^ n) (pow_integralUnitExponent_mem u)
  simp only [map_pow, toAdd_pow, nsmul_eq_mul] at hpower
  change Multiplicative.toAdd (f u) = log1p (((u ^ n).val : K) - 1) / (n : K)
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using hpower

/-- The image is compact because it is the continuous image of the actual
full integral unit group. No compactness field is supplied. -/
theorem isCompact_unitLog_range : IsCompact (Set.range (unitLog (K := K))) := by
  letI := compactSpace_units (K := K)
  simpa only [Set.image_univ] using isCompact_univ.image (continuous_unitLog (p := p))

omit localNormedAlgebra in
/-- The paper's factor is p for odd p, and p² at p=2. -/
def logShellScale (p : ℕ) : ℕ := if p = 2 then p ^ 2 else p

/-- The paper's actual scaled logarithmic image as an additive subgroup. -/
def integralLogShell : AddSubgroup K where
  carrier := Set.range (fun u : (Integers K)ˣ =>
    (logShellScale p : K)⁻¹ * unitLog u)
  zero_mem' := ⟨1, by dsimp only; rw [unitLog_one (p := p), mul_zero]⟩
  add_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, by dsimp only; rw [unitLog_mul (p := p), mul_add]⟩
  neg_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u⁻¹, by dsimp only; rw [unitLog_inv (p := p), mul_neg]⟩

/-- Compactness of the actual source image `(p*)⁻¹ log(O_kˣ)`. -/
theorem isCompact_integralLogShell :
    IsCompact (integralLogShell (K := K) (p := p) : Set K) := by
  letI := compactSpace_units (K := K)
  change IsCompact (Set.range (fun u : (Integers K)ˣ =>
    (logShellScale p : K)⁻¹ * unitLog u))
  have hc : Continuous (fun u : (Integers K)ˣ => (logShellScale p : K)⁻¹ * unitLog u) :=
    continuous_const.mul (continuous_unitLog (p := p))
  simpa only [Set.image_univ] using isCompact_univ.image hc

end

end LeanFormal.IUT.LocalFieldLogarithm
