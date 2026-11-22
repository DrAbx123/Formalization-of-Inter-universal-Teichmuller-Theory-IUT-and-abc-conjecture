import tmp.sheaf.n8.closure.NativeInput
import LeanFormal.IUT.Foundations.NumberField.Places
import Mathlib.Data.Finsupp.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Global realified Frobenioid C^⊩mod: actual carrier data

Source: IUT III, Example 3.6 and §1-2.  The global realified Frobenioid C^⊩mod
has base category the category with precisely one arrow, prime objects naturally
indexed by the places Vmod of Fmod, and a realified divisor monoid.

This file constructs the actual carrier data available from the source:
* the one-arrow base category;
* the global realified divisor monoid on NumberFieldPlace Fmod (finite support);
* the prime divisor attached to each place;
* the realified degree as the arithmetic weighted degree;
* a constant value functor.

This is the actual carrier layer.  The full FrobenioidPresentation axioms and
the q_v zero-locus divisor are separate; no fake equality/inequality is asserted.

No toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput

universe u

/-- The one-arrow base category of C^⊩mod. -/
abbrev GlobalBaseCategory : Type := CategoryTheory.SingleObj Unit

/-- The base category has one object. -/
theorem globalBaseCategory_one_object (X Y : GlobalBaseCategory) : X = Y :=
  Subsingleton.elim X Y

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The global prime index: all places of the base number field Fmod. -/
abbrev GlobalPrimeIndex : Type := NumberFieldPlace X.S.arithmetic.Fmod

/-- The actual realified divisor group carried by C^⊩mod: finitely supported
real coefficients on the global places. -/
abbrev GlobalDivisorGroup : Type := GlobalPrimeIndex (X := X) →₀ Real

/-- The multiplicative realified divisor monoid. -/
abbrev GlobalDivisorMonoid : Type := Multiplicative (GlobalDivisorGroup (X := X))

/-- Arithmetic degree weight of a global prime place: log absolute norm at
finite places, and 1 at infinite places (the realified archimedean weight). -/
noncomputable def globalPrimeWeight : GlobalPrimeIndex (X := X) → Real
  | NumberFieldPlace.finite p =>
      Real.log (Ideal.absNorm p.maximalIdeal.asIdeal : Real)
  | NumberFieldPlace.infinite _ => 1

/-- The realified degree of a finite-support global divisor: the weighted sum of
its coefficients. -/
noncomputable def globalDegreeFun (D : GlobalDivisorGroup (X := X)) : Real :=
  D.sum fun v c => c * globalPrimeWeight (X := X) v

/-- The realified degree homomorphism on the multiplicative divisor monoid. -/
noncomputable def globalDegree :
    GlobalDivisorMonoid (X := X) →* Multiplicative Real where
  toFun D := Multiplicative.ofAdd (globalDegreeFun (X := X) D.toAdd)
  map_one' := by
    simp [globalDegreeFun]
  map_mul' D E := by
    classical
    change Multiplicative.ofAdd
        (globalDegreeFun (X := X)
          (Multiplicative.toAdd D + Multiplicative.toAdd E)) =
      Multiplicative.ofAdd
          (globalDegreeFun (X := X) (Multiplicative.toAdd D)) *
        Multiplicative.ofAdd
          (globalDegreeFun (X := X) (Multiplicative.toAdd E))
    unfold globalDegreeFun
    rw [Finsupp.sum_add_index (fun v => by simp)
      (fun v a b => by intro c; ring)]
    simp [map_add]

/-- The prime divisor object attached to a global place. -/
noncomputable def globalPrimeDivisor (v : GlobalPrimeIndex (X := X)) :
    GlobalDivisorMonoid (X := X) :=
  Multiplicative.ofAdd (Finsupp.single v 1)

/-- The prime divisor has weighted degree equal to the arithmetic weight of the
place. -/
theorem globalDegree_primeDivisor (v : GlobalPrimeIndex (X := X)) :
    globalDegree (X := X) (globalPrimeDivisor (X := X) v) =
      Multiplicative.ofAdd (globalPrimeWeight (X := X) v) := by
  classical
  change Multiplicative.ofAdd
      ((Finsupp.single v 1).sum
        (fun w c => c * globalPrimeWeight (X := X) w)) =
    Multiplicative.ofAdd (globalPrimeWeight (X := X) v)
  simp

/-- Actual carrier of the global realified Frobenioid C^⊩mod. -/
structure GlobalRealifiedFrobenioidCarrier where
  baseCategory : Type u
  [category : CategoryTheory.Category baseCategory]
  primeIndex : Type u
  divisorMonoid : Type u
  [commMonoid : CommMonoid divisorMonoid]
  valueFunctor : CategoryTheory.Functor baseCategory Type
  degree : divisorMonoid →* Multiplicative Real
  realification : divisorMonoid → Real
  realification_mul : ∀ a b, realification (a * b) = realification a + realification b
  degree_realification : ∀ a, (degree a : Real) = realification a
  unit : divisorMonoid
  unit_realification : realification 1 = 0
  primeObject : primeIndex → divisorMonoid

attribute [instance] GlobalRealifiedFrobenioidCarrier.category
attribute [instance] GlobalRealifiedFrobenioidCarrier.commMonoid

/-- The actual global realified Frobenioid carrier from the source places. -/
noncomputable def globalRealifiedFrobenioidCarrier (X : N8NativeInput l) :
    GlobalRealifiedFrobenioidCarrier where
  baseCategory := GlobalBaseCategory
  category := inferInstance
  primeIndex := GlobalPrimeIndex (X := X)
  divisorMonoid := GlobalDivisorMonoid (X := X)
  commMonoid := inferInstance
  valueFunctor := (CategoryTheory.Functor.const (J := GlobalBaseCategory) (C := Type)).obj
    (GlobalDivisorMonoid (X := X))
  degree := globalDegree (X := X)
  realification := fun D => (globalDegree (X := X) D : Real)
  realification_mul := by
    intro a b
    rw [map_mul]
    rfl
  degree_realification := fun _ => rfl
  unit := 1
  unit_realification := by
    change Multiplicative.ofAdd (globalDegreeFun (X := X) 0) = 1
    simp [globalDegreeFun]
  primeObject := globalPrimeDivisor (X := X)

/-- The carrier's base category is the one-arrow category. -/
theorem globalRealifiedFrobenioidCarrier_base :
    (globalRealifiedFrobenioidCarrier (X := X)).baseCategory = GlobalBaseCategory := rfl

/-- The carrier's prime index is the actual global place type. -/
theorem globalRealifiedFrobenioidCarrier_primeIndex :
    (globalRealifiedFrobenioidCarrier (X := X)).primeIndex =
      GlobalPrimeIndex (X := X) := rfl

/-- The carrier's divisor monoid is the actual global realified divisor monoid. -/
theorem globalRealifiedFrobenioidCarrier_divisorMonoid :
    (globalRealifiedFrobenioidCarrier (X := X)).divisorMonoid =
      GlobalDivisorMonoid (X := X) := rfl

/-- The carrier's prime object is the actual prime divisor. -/
theorem globalRealifiedFrobenioidCarrier_primeObject (v : GlobalPrimeIndex (X := X)) :
    (globalRealifiedFrobenioidCarrier (X := X)).primeObject v =
      globalPrimeDivisor (X := X) v := rfl

/-! ## Exact missing full object

Constructed here: actual one-arrow base category, global finite-support
realified divisor monoid, prime divisors, arithmetic realified degree, and value
functor carrier.

Not constructed: the full categorical FrobenioidPresentation with all
FrobenioidAxioms; the q_v family over V_bad; and the q_v zero-locus arithmetic
divisor in this carrier.  Those remain separate source obligations. -/

end LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual

end
