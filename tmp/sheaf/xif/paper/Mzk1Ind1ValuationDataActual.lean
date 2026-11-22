import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import tmp.sheaf.xif.paper.Mzk1Ind1InfiniteDivisibleActual
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1ValuationDataActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1InfiniteDivisibleActual
open scoped Valued

variable {F : Type} [NormedField F] [IsUltrametricDist F]

/-- `A_F = F^× / μ(F)`. -/
abbrev AQuotient (F : Type) [Field F] : Type := TimesMuQuotient Fˣ

instance wQuotientTorsionNormal (F : Type) [NormedField F]
    [IsUltrametricDist F] :
    (CommGroup.torsion (Integers F)ˣ).Normal :=
  Subgroup.normal_of_comm _

/-- `W_F = O_F^× / μ(F)`. -/
abbrev WQuotient (F : Type) [NormedField F] [IsUltrametricDist F] : Type :=
  (Integers F)ˣ ⧸ CommGroup.torsion (Integers F)ˣ


/-- Units of the valued field mapped into the units of `WithZero (Multiplicative ℤ)`. -/
def unitsToValuedUnits [Valued F (WithZero (Multiplicative ℤ))] :
    Fˣ →* (WithZero (Multiplicative ℤ))ˣ where
  toFun u := Units.mk0 (Valued.v (u : F))
    ((Valuation.ne_zero_iff _).mpr (Units.ne_zero u))
  map_one' := by ext; simp
  map_mul' := by intro u v; ext; simp [map_mul]

/-- The actual unit valuation coming from `Valued.v`, using the unit/zero
equivalence on `WithZero (Multiplicative ℤ)`. -/
def unitValuationHom [Valued F (WithZero (Multiplicative ℤ))] :
    Fˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (unitsToValuedUnits (F := F))
/-- Exact valuation donor needed for §5.1: a hom `A_F → Multiplicative ℤ`
whose kernel is the image of `W_F`, together with the infinite `r`-divisibility
of `W_F` for all `r` coprime to `p`.  No inhabitant is supplied. -/
structure LocalValuationData (F : Type) [NormedField F] [IsUltrametricDist F]
    (p : Nat) where
  unitToA : WQuotient F →* AQuotient F
  v : AQuotient F →* Multiplicative ℤ
  range_unitToA_eq_ker : unitToA.range = v.ker
  infinitelyDivisible : ∀ r : Nat, Nat.Coprime r p →
    ∀ x : WQuotient F, InfinitelyDivisibleFor r x

def LocalValuationDataRequired (F : Type) [NormedField F] [IsUltrametricDist F]
    (p : Nat) : Prop :=
  Nonempty (LocalValuationData F p)

#print axioms LocalValuationDataRequired

lemma multiplicative_int_eq_one_of_pow_eq_one (a : Multiplicative ℤ)
    {n : Nat} (hn : 0 < n) (h : a ^ n = 1) : a = 1 := by
  have hk : n • a.toAdd = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  have hk0 : a.toAdd = 0 := by
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hmul : (n : ℤ) * a.toAdd = 0 := by
      simpa [nsmul_eq_mul] using hk
    exact (mul_eq_zero.mp hmul).resolve_left hn'
  exact Multiplicative.toAdd.injective (by simpa using hk0)

theorem torsion_le_ker_unitValuationHom [Valued F (WithZero (Multiplicative ℤ))] :
    CommGroup.torsion Fˣ ≤ (unitValuationHom (F := F)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rcases isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion x).mp hx) with
    ⟨n, hnpos, hpow⟩
  have hm : (unitValuationHom (F := F) x) ^ n = 1 := by
    simpa [map_pow] using
      congrArg (unitValuationHom (F := F)) hpow
  exact multiplicative_int_eq_one_of_pow_eq_one _ hnpos hm



theorem unitValuationHom_eq_one_iff [Valued F (WithZero (Multiplicative ℤ))]
    (u : Fˣ) :
    unitValuationHom (F := F) u = 1 ↔ Valued.v (u : F) = 1 := by
  constructor
  · intro h
    have h' : unitsToValuedUnits (F := F) u = 1 := by
      apply WithZero.unitsWithZeroEquiv.injective
      calc
        WithZero.unitsWithZeroEquiv (unitsToValuedUnits (F := F) u) =
            unitValuationHom (F := F) u := rfl
        _ = 1 := h
        _ = WithZero.unitsWithZeroEquiv (1 : (WithZero (Multiplicative ℤ))ˣ) :=
            by rw [WithZero.unitsWithZeroEquiv.map_one]
    have hv := congrArg Units.val h'
    simpa [unitsToValuedUnits, Units.val_mk0] using hv
  · intro h
    have h' : unitsToValuedUnits (F := F) u = 1 := by
      apply Units.ext
      simpa [unitsToValuedUnits, h]
    calc
      unitValuationHom (F := F) u =
          WithZero.unitsWithZeroEquiv (unitsToValuedUnits (F := F) u) := rfl
      _ = WithZero.unitsWithZeroEquiv (1 : (WithZero (Multiplicative ℤ))ˣ) := by rw [h']
      _ = 1 := by rw [WithZero.unitsWithZeroEquiv.map_one]

#print axioms unitValuationHom_eq_one_iff

def quotientValuationHom [Valued F (WithZero (Multiplicative ℤ))]
    (h : CommGroup.torsion Fˣ ≤ (unitValuationHom (F := F)).ker) :
    AQuotient F →* Multiplicative ℤ :=
  QuotientGroup.lift (CommGroup.torsion Fˣ) (unitValuationHom (F := F)) h

#print axioms torsion_le_ker_unitValuationHom
end LeanFormal.IUT.XiFPaper.Mzk1Ind1ValuationDataActual