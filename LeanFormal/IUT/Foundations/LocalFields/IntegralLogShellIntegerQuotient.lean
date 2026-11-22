import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmTorsionFinite
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmOpenMap

/-!
# The actual quotient of the logarithmic shell by valuation integers

The integer subgroup is the actual preimage of O in the constructed shell.
Compactness and openness prove that its additive quotient is finite. The
full-unit scaled logarithm gives a surjective map to this quotient, which
factors through the actual finite p*-congruence quotient.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

def logShellIntegerSubgroup : AddSubgroup (integralLogShell (K := K) (p := p)) :=
  (Integers K).toAddSubgroup.comap (integralLogShell (K := K) (p := p)).subtype

abbrev LogShellIntegerQuotient :=
  integralLogShell (K := K) (p := p) ⧸ logShellIntegerSubgroup (K := K) (p := p)

theorem mem_logShellIntegerSubgroup_iff (x : integralLogShell (K := K) (p := p)) :
    x ∈ logShellIntegerSubgroup (K := K) (p := p) ↔ (x : K) ∈ Integers K := Iff.rfl

theorem isOpen_logShellIntegerSubgroup :
    IsOpen (logShellIntegerSubgroup (K := K) (p := p) :
      Set (integralLogShell (K := K) (p := p))) := by
  have hO : IsOpen (Integers K : Set K) := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    have hsmall : ‖y - x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    apply (mem_integers_iff _).mpr
    calc
      ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ max ‖y - x‖ ‖x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hsmall.le ((mem_integers_iff _).mp hx)
  exact hO.preimage continuous_subtype_val

theorem finite_logShellIntegerQuotient : Finite (LogShellIntegerQuotient (K := K) (p := p)) := by
  letI : CompactSpace (integralLogShell (K := K) (p := p)) :=
    isCompact_iff_compactSpace.mp (isCompact_integralLogShell (K := K) (p := p))
  letI := QuotientAddGroup.discreteTopology (N := logShellIntegerSubgroup (K := K) (p := p))
    isOpen_logShellIntegerSubgroup
  exact finite_of_compact_of_discrete

def logShellIntegerIndex : ℕ := Nat.card (LogShellIntegerQuotient (K := K) (p := p))

theorem logShellIntegerIndex_pos : 0 < logShellIntegerIndex (K := K) (p := p) := by
  letI := finite_logShellIntegerQuotient (K := K) (p := p)
  exact Nat.card_pos

def scaledUnitLogToShellHom :
    (Integers K)ˣ →* Multiplicative (integralLogShell (K := K) (p := p)) where
  toFun u := Multiplicative.ofAdd ⟨(logShellScale p : K)⁻¹ * unitLog u, ⟨u, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change (logShellScale p : K)⁻¹ * unitLog (1 : (Integers K)ˣ) = 0
    rw [unitLog_one (p := p), mul_zero]
  map_mul' u v := by
    apply Subtype.ext
    change (logShellScale p : K)⁻¹ * unitLog (u * v) =
      (logShellScale p : K)⁻¹ * unitLog u + (logShellScale p : K)⁻¹ * unitLog v
    rw [unitLog_mul (p := p), mul_add]

theorem scaledUnitLogToShellHom_surjective :
    Function.Surjective (scaledUnitLogToShellHom (K := K) (p := p)) := by
  intro x
  rcases (Multiplicative.toAdd x).property with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hu

def unitLogIntegerQuotientHom :
    (Integers K)ˣ →* Multiplicative (LogShellIntegerQuotient (K := K) (p := p)) :=
  (AddMonoidHom.toMultiplicative
    (QuotientAddGroup.mk' (logShellIntegerSubgroup (K := K) (p := p)))).comp
      (scaledUnitLogToShellHom (K := K) (p := p))

theorem unitLogIntegerQuotientHom_surjective :
    Function.Surjective (unitLogIntegerQuotientHom (K := K) (p := p)) := by
  have hquotient : Function.Surjective (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' (logShellIntegerSubgroup (K := K) (p := p)))) := by
    change Function.Surjective (QuotientAddGroup.mk : integralLogShell (K := K) (p := p) →
      LogShellIntegerQuotient (K := K) (p := p))
    intro x
    exact Quotient.inductionOn' x (fun y => ⟨y, rfl⟩)
  exact hquotient.comp scaledUnitLogToShellHom_surjective

theorem logShellCongruenceUnits_le_unitLogIntegerQuotientHom_ker :
    logShellCongruenceUnits (K := K) (p := p) ≤
      (unitLogIntegerQuotientHom (K := K) (p := p)).ker := by
  intro u hu
  change QuotientAddGroup.mk (Multiplicative.toAdd (scaledUnitLogToShellHom (p := p) u)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  change (logShellScale p : K)⁻¹ * unitLog u ∈ Integers K
  exact scaledUnitLog_mem_integers_of_mem_congruence u hu

def congruenceQuotientToLogShellIntegers :
    ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) →*
      Multiplicative (LogShellIntegerQuotient (K := K) (p := p)) :=
  QuotientGroup.lift _ (unitLogIntegerQuotientHom (K := K) (p := p))
    logShellCongruenceUnits_le_unitLogIntegerQuotientHom_ker

theorem congruenceQuotientToLogShellIntegers_surjective :
    Function.Surjective (congruenceQuotientToLogShellIntegers (K := K) (p := p)) := by
  intro x
  obtain ⟨u, hu⟩ := unitLogIntegerQuotientHom_surjective (K := K) (p := p) x
  exact ⟨QuotientGroup.mk u, hu⟩

def torsionToIntegerQuotientKernelHom : CommGroup.torsion (Integers K)ˣ →*
    (congruenceQuotientToLogShellIntegers (K := K) (p := p)).ker where
  toFun u := ⟨torsionCongruenceHom (p := p) u, by
    have hu : unitLog u.val = 0 :=
      (unitLog_eq_zero_iff_isOfFinOrder (p := p) u.val).mpr u.property
    change QuotientAddGroup.mk (Multiplicative.toAdd (scaledUnitLogToShellHom (p := p) u.val)) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    change (logShellScale p : K)⁻¹ * unitLog u.val ∈ Integers K
    rw [hu, mul_zero]
    exact (Integers K).zero_mem⟩
  map_one' := Subtype.ext (map_one (torsionCongruenceHom (K := K) (p := p)))
  map_mul' u v := Subtype.ext (map_mul (torsionCongruenceHom (K := K) (p := p)) u v)

theorem torsionToIntegerQuotientKernelHom_injective :
    Function.Injective (torsionToIntegerQuotientKernelHom (K := K) (p := p)) := by
  intro u v h
  apply torsionCongruenceHom_injective (p := p)
  exact congrArg Subtype.val h

theorem torsionToIntegerQuotientKernelHom_surjective :
    Function.Surjective (torsionToIntegerQuotientKernelHom (K := K) (p := p)) := by
  intro q
  have hrepresentative : ∃ u : (Integers K)ˣ,
      (QuotientGroup.mk u : (Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) = q.val :=
    Quotient.inductionOn' q.val (fun u => ⟨u, rfl⟩)
  obtain ⟨u, hu⟩ := hrepresentative
  have hquotient : unitLogIntegerQuotientHom (K := K) (p := p) u = 1 := by
    have hkernel := q.property
    change congruenceQuotientToLogShellIntegers (K := K) (p := p) q.val = 1 at hkernel
    rw [← hu] at hkernel
    exact hkernel
  have hx : (logShellScale p : K)⁻¹ * unitLog u ∈ Integers K := by
    change QuotientAddGroup.mk (Multiplicative.toAdd (scaledUnitLogToShellHom (p := p) u)) = 0
      at hquotient
    rw [QuotientAddGroup.eq_zero_iff] at hquotient
    exact hquotient
  obtain ⟨w, hw, hwlog⟩ := exists_congruenceUnitLog_eq_scale_mul (p := p)
    (⟨(logShellScale p : K)⁻¹ * unitLog u, hx⟩ : Integers K)
  have hscale : (logShellScale p : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (logShellScale_pos (p := p)).ne'
  have hwlogeq : unitLog w = unitLog u := by
    simpa only [mul_inv_cancel_left₀ hscale] using hwlog
  have hzero : unitLog (u * w⁻¹) = 0 := by
    rw [unitLog_mul (p := p), unitLog_inv (p := p), hwlogeq, add_neg_cancel]
  let torsionUnit : CommGroup.torsion (Integers K)ˣ :=
    ⟨u * w⁻¹, (unitLog_eq_zero_iff_isOfFinOrder (p := p) _).mp hzero⟩
  refine ⟨torsionUnit, ?_⟩
  apply Subtype.ext
  change (QuotientGroup.mk (u * w⁻¹) :
    (Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) = q.val
  have hwquotient : (QuotientGroup.mk w :
      (Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact hw
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwquotient, inv_one, mul_one, hu]

def torsionIntegerQuotientKernelEquiv : CommGroup.torsion (Integers K)ˣ ≃*
    (congruenceQuotientToLogShellIntegers (K := K) (p := p)).ker :=
  MulEquiv.ofBijective (torsionToIntegerQuotientKernelHom (K := K) (p := p))
    ⟨torsionToIntegerQuotientKernelHom_injective, torsionToIntegerQuotientKernelHom_surjective⟩

theorem card_logShellCongruenceQuotient :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      Nat.card (CommGroup.torsion (Integers K)ˣ) * logShellIntegerIndex (K := K) (p := p) := by
  let quotientHom := congruenceQuotientToLogShellIntegers (K := K) (p := p)
  have hquotient :
      Nat.card (((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ⧸ quotientHom.ker) =
        Nat.card (LogShellIntegerQuotient (K := K) (p := p)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective quotientHom
      congruenceQuotientToLogShellIntegers_surjective).toEquiv
  have hkernel : Nat.card quotientHom.ker = Nat.card (CommGroup.torsion (Integers K)ˣ) :=
    Nat.card_congr (torsionIntegerQuotientKernelEquiv (K := K) (p := p)).toEquiv.symm
  rw [quotientHom.ker.card_eq_card_quotient_mul_card_subgroup, hquotient, hkernel]
  exact Nat.mul_comm _ _

end

end LeanFormal.IUT.LocalFieldLogarithm
