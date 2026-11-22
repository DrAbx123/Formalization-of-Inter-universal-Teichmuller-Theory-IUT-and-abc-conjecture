import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Int

/-!
# S397: explicit single-stage CharacteristicSplitting tau data

One-object D model with endomorphism monoid U x Multiplicative Z, where U is the
unit group and pi = (1, ofAdd 1) is the valuation-one uniformizer.  The
characteristic submonoid is

  tau = { pi^n | n in Z } = { (1, e) }.

The unit embedding is u |-> (u,0).  Multiplication

  Units x tau -> M,  (u, pi^n) |-> u * pi^n

is bijective; the inverse is m |-> (m.1, pi^(val m)).  units_commute holds
because M is commutative.  This is an explicit parameter model (U is a
parameter), not a fake carrier and not the missing S396 transport.

No inequality is stated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

namespace LeanFormal.IUT.XiFPaper.S397SingleStageTauCharacteristicActual

open CategoryTheory

universe u

variable (U : Type u) [CommGroup U]

/-- The one-object D model's endomorphism monoid: units times the uniformizer
exponent group. -/
abbrev StageUnitMonoid : Type u := U × Multiplicative ℤ

noncomputable instance stageUnitMonoidCommGroup :
    CommGroup (StageUnitMonoid U) := inferInstance

/-- The one-object category D. -/
abbrev StageOneObjectD : Type :=
  CategoryTheory.SingleObj Unit

/-- D has exactly one object. -/
theorem stageOneObject_subsingleton (X Y : StageOneObjectD) : X = Y :=
  Subsingleton.elim X Y

/-- The valuation-one uniformizer pi = (1, 1). -/
noncomputable def stagePi : StageUnitMonoid U :=
  (1, Multiplicative.ofAdd (1 : ℤ))

/-- Valuation of the model monoid: the uniformizer exponent. -/
def stageValuation (x : StageUnitMonoid U) : ℤ :=
  Multiplicative.toAdd x.2

/-- pi has valuation one. -/
theorem stageValuation_pi : stageValuation U (stagePi U) = 1 := rfl

/-- Units embed with valuation zero. -/
noncomputable def stageUnitEmbedding (u : U) : StageUnitMonoid U :=
  (u, Multiplicative.ofAdd (0 : ℤ))

/-- The valuation of an embedded unit is zero. -/
theorem stageValuation_unit (u : U) :
    stageValuation U (stageUnitEmbedding U u) = 0 := rfl

/-- tau = { (1,e) | e in Z }. -/
def stageTau : Submonoid (StageUnitMonoid U) where
  carrier := {x | x.1 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    show a.1 * b.1 = 1
    rw [ha, hb, one_mul]

/-- tau is exactly the integer powers of pi. -/
theorem stageTau_eq_zpow :
    stageTau U = {x : StageUnitMonoid U | ∃ n : ℤ, x = stagePi U ^ n} := by
  ext x
  constructor
  · intro hx
    change x.1 = 1 at hx
    refine ⟨Multiplicative.toAdd x.2, ?_⟩
    ext
    · simpa [stagePi] using hx
    · simp [stagePi]
  · rintro ⟨n, rfl⟩
    simp [stageTau, stagePi]

/-- Every pi^n lies in tau. -/
theorem stagePi_zpow_mem_tau (n : ℤ) : stagePi U ^ n ∈ stageTau U := by
  show stagePi U ^ n ∈ (stageTau U : Set (StageUnitMonoid U))
  rw [stageTau_eq_zpow]
  exact ⟨n, rfl⟩

/-- Embedding of a unit times a tau element. -/
noncomputable def stageUnitTauMul :
    U × stageTau U → StageUnitMonoid U :=
  fun p => stageUnitEmbedding U p.1 * p.2.1

/-- The unit-plus-pi^n decomposition is bijective. -/
theorem stageUnitTauMul_bijective :
    Function.Bijective (stageUnitTauMul U) := by
  constructor
  · intro p q h
    apply Prod.ext
    · have hp : (p.2.1).1 = 1 := p.2.2
      have hq : (q.2.1).1 = 1 := q.2.2
      have h1 := congrArg Prod.fst h
      simpa [stageUnitTauMul, stageUnitEmbedding, hp, hq] using h1
    · have h2 := congrArg (fun x : StageUnitMonoid U => x.2) h
      have hp2 : (p.2.1).1 = 1 := p.2.2
      have hq2 : (q.2.1).1 = 1 := q.2.2
      exact Subtype.ext (Prod.ext (by rw [hp2, hq2])
        (by simpa [stageUnitTauMul, stageUnitEmbedding] using h2))
  · intro x
    refine ⟨(x.1, ⟨(1, x.2), ?_⟩), ?_⟩
    · simp [stageTau]
    · simp [stageUnitTauMul, stageUnitEmbedding, one_mul]

/-- The unit group commutes with every tau element. -/
theorem stageUnits_commute
    (u : U) (characteristic : stageTau U) :
    Commute (stageUnitEmbedding U u) (characteristic : StageUnitMonoid U) :=
  Commute.all _ _

/-- Explicit single-stage tau part of a CharacteristicSplitting.

This is a LOCAL CANDIDATE for the one-object model only.  The paper split
Frobenioid base is D_v^⊢ (finite etale covers), not this one-object D; this
structure must not be connected to the paper target. -/
structure SingleStageCharacteristicTauPart (U : Type u) [CommGroup U] where
  oneObjectD : Type
  oneObject_subsingleton : ∀ X Y : oneObjectD, X = Y
  pi : StageUnitMonoid U
  valuation : StageUnitMonoid U → ℤ
  valuation_pi : valuation pi = 1
  tau : Submonoid (StageUnitMonoid U)
  tau_eq_zpow : tau = {x : StageUnitMonoid U | ∃ n : ℤ, x = pi ^ n}
  units_commute : ∀ (u : U) (characteristic : tau),
    Commute (stageUnitEmbedding U u) (characteristic : StageUnitMonoid U)
  multiplication_bijective :
    Function.Bijective (fun pair : U × tau =>
      stageUnitEmbedding U pair.1 * pair.2.1)

/-- Actual explicit model constructor. -/
noncomputable def singleStageCharacteristicTauPart (U : Type u) [CommGroup U] :
    SingleStageCharacteristicTauPart U where
  oneObjectD := StageOneObjectD
  oneObject_subsingleton := stageOneObject_subsingleton
  pi := stagePi U
  valuation := stageValuation U
  valuation_pi := stageValuation_pi U
  tau := stageTau U
  tau_eq_zpow := stageTau_eq_zpow U
  units_commute := stageUnits_commute U
  multiplication_bijective := stageUnitTauMul_bijective U

end LeanFormal.IUT.XiFPaper.S397SingleStageTauCharacteristicActual

end
