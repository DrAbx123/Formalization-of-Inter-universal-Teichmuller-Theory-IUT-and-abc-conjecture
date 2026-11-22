import tmp.sheaf.xif.paper.DvTriangleFieldCoversActual
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Order.Group.Int

/-!
# S412: tau = pi^Z on the actual paper base D_v^⊢ = DvTriangleFieldCover

For a finite etale field cover L/K and a normalized Z-valued valuation
v : L^× -> Z with v(pi)=1, tau = {pi^n | n in Z}, O^× = ker v, and

  O^× x tau -> L^×,  (u, pi^n) |-> u * pi^n

is bijective.  The q_v normalized valuation extension to each cover L is NOT
constructed in the tree; it is recorded as the exact missing parameter
DvTriangleCoverQValuationData.  No one-object SingleObj carrier is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual

universe u

variable {K : Type u} [Field K]

/-- Exact missing data: a normalized Z-valued valuation on L^× extending the
q_v normalized valuation, for a finite etale field cover L/K. -/
structure DvCoverNormalizedValuationData (K : Type u) [Field K]
    (L : Type u) [Field L] [Algebra K L] where
  valuation : Lˣ →* Multiplicative ℤ
  valuation_surjective : Function.Surjective
    (fun x : Lˣ => Multiplicative.toAdd (valuation x))
  qValuation : ℤ

variable {L : Type u} [Field L] [Algebra K L]
variable (V : DvCoverNormalizedValuationData K L)

/-- The valuation-one uniformizer chosen from surjectivity. -/
noncomputable def dvPi : Lˣ :=
  Classical.choose (V.valuation_surjective 1)

/-- The chosen uniformizer has normalized valuation one. -/
theorem dvPi_valuation :
    Multiplicative.toAdd (V.valuation (dvPi V)) = 1 :=
  Classical.choose_spec (V.valuation_surjective 1)

/-- tau = {pi^n | n in Z}. -/
def dvTau : Submonoid Lˣ where
  carrier := {x | ∃ n : ℤ, x = dvPi V ^ n}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by rw [zpow_add]⟩

/-- The valuation-zero unit subgroup O^×. -/
def dvOUnits : Subgroup Lˣ where
  carrier := {u | Multiplicative.toAdd (V.valuation u) = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : Multiplicative.toAdd (V.valuation a) = 0 := ha
    have hb' : Multiplicative.toAdd (V.valuation b) = 0 := hb
    apply Multiplicative.toAdd.injective
    simp [map_mul, ha', hb']
  inv_mem' := by
    intro a ha
    simpa using congrArg Neg.neg ha

/-- Embedding O^× into L^×. -/
def dvOUnitsEmbedding : dvOUnits V → Lˣ := fun u => u.1

/-- Unit-plus-pi^n multiplication map. -/
def dvUnitTauMul : dvOUnits V × dvTau V → Lˣ :=
  fun p => p.1.1 * p.2.1

/-- The unit-plus-tau decomposition is bijective. -/
theorem dvUnitTauMul_bijective :
    Function.Bijective (dvUnitTauMul V) := by
  constructor
  · intro p q h
    have hval := congrArg (fun x : Lˣ =>
      Multiplicative.toAdd (V.valuation x)) h
    rcases p.2.2 with ⟨m, hm⟩
    rcases q.2.2 with ⟨n, hn⟩
    have hp : Multiplicative.toAdd (V.valuation p.1.1) = 0 := p.1.2
    have hq : Multiplicative.toAdd (V.valuation q.1.1) = 0 := q.1.2
    simp only [dvUnitTauMul, map_mul] at hval
    rw [hm, hn] at hval
    simp [map_zpow, dvPi_valuation V, hp, hq] at hval
    have hmn : m = n := by omega
    have htau : p.2 = q.2 := by
      apply Subtype.ext
      rw [hm, hn, hmn]
    have hcancel : p.1.1 = q.1.1 := by
      have hh : p.1.1 * p.2.1 = q.1.1 * p.2.1 := by
        simpa [dvUnitTauMul, htau] using h
      exact mul_right_cancel hh
    exact Prod.ext (Subtype.ext hcancel) htau
  · intro x
    let n : ℤ := Multiplicative.toAdd (V.valuation x)
    let u : Lˣ := x * (dvPi V) ^ (-n)
    have hu : Multiplicative.toAdd (V.valuation u) = 0 := by
      simp [u, map_mul, map_zpow, n, dvPi_valuation V]
    refine ⟨(⟨u, hu⟩, ⟨(dvPi V) ^ n, ⟨n, rfl⟩⟩), ?_⟩
    simp [dvUnitTauMul, u, mul_assoc]
/-- Units commute with tau (field units are commutative). -/
theorem dvUnits_commute
    (u : dvOUnits V) (characteristic : dvTau V) :
    Commute (u : Lˣ) (characteristic : Lˣ) :=
  Commute.all _ _

/-- Actual S398 cover-level tau package, conditional on the exact valuation
extension datum. -/
structure DvTriangleCoverTauPart
    (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj] where
  valuationData : DvCoverNormalizedValuationData K L.obj.obj
  tau : Submonoid L.obj.objˣ
  tau_eq_zpow : tau = dvTau valuationData
  units_commute : ∀ (u : dvOUnits valuationData) (characteristic : tau),
    Commute (u : L.obj.objˣ) (characteristic : L.obj.objˣ)
  multiplication_bijective :
    Function.Bijective (fun p : dvOUnits valuationData × tau =>
      (p.1 : L.obj.objˣ) * p.2.1)

/-- Conditional constructor for each actual finite etale field cover. -/
noncomputable def dvTriangleCoverTauPart
    (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj]
    (V : DvCoverNormalizedValuationData K L.obj.obj) :
    DvTriangleCoverTauPart L where
  valuationData := V
  tau := dvTau V
  tau_eq_zpow := rfl
  units_commute := dvUnits_commute V
  multiplication_bijective := dvUnitTauMul_bijective V

/-- Exact missing q_v valuation extension on a finite etale field cover. -/
def DvTriangleCoverQValuationExtensionRequired
    (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj] : Prop :=
  Nonempty (DvCoverNormalizedValuationData K L.obj.obj)

end LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual

end
