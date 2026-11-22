import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.C3Roots
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTII.Kummer.KummerClass
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib

/-!
# Native C3 slice: actual q, roots, Kummer class, tensor landing

This file starts from the native selected bad place and constructs the actual
q from a source Tate comparison witness (source curve/Tate data), roots in the
algebraic closure, and the Kummer class/root-change towers.

The remaining tensor landing is an exact missing production declaration: the
repository has no NumberFieldFinitePlace.Completion -> ArithmeticTensorTupleBlock map.
No uniformizer/proxy is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeC3

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace

universe u ua uv upi umon ui v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- A bad base finite place selected from native nonemptiness. -/
noncomputable def nativeBadBasePlace : NumberField.FinitePlace X.S.arithmetic.Fmod :=
  Classical.choose (show ∃ x, x ∈ X.S.tuple.source.V_mod_bad from
    X.S.tuple.source.V_mod_bad_nonempty)

theorem nativeBadBasePlace_mem :
    nativeBadBasePlace X ∈ X.S.tuple.source.V_mod_bad :=
  Classical.choose_spec (show ∃ x, x ∈ X.S.tuple.source.V_mod_bad from
    X.S.tuple.source.V_mod_bad_nonempty)

/-- A finite F-place over the native selected bad base place. -/
noncomputable def nativeFPlaceOverBad : NumberField.FinitePlace X.S.arithmetic.F :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective (K := X.S.arithmetic.F) (nativeBadBasePlace X))

theorem nativeFPlaceOverBad_comap :
    NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X) = nativeBadBasePlace X :=
  by
    simpa [nativeFPlaceOverBad] using
      Classical.choose_spec
        (NumberFieldFinitePlace.comap_surjective (K := X.S.arithmetic.F)
          (nativeBadBasePlace X))

theorem nativeFPlaceOverBad_mem_bad :
    NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X) ∈ X.S.tuple.source.V_mod_bad := by
  rw [nativeFPlaceOverBad_comap X]
  exact nativeBadBasePlace_mem X

/-- Exact source q donor: a Tate curve comparison witness at the native
F-place over the selected bad base place. -/
structure NativeQDonor where
  witness : SourceTateComparisonWitness X.S.arithmetic (nativeFPlaceOverBad X)


/-- The actual Tate comparison witness comes from the native Clause (b);
no external donor is needed. -/
noncomputable def nativeQDonorActual : NativeQDonor X :=
  ⟨Classical.choice
    (X.S.clauseB.q_comparison (nativeFPlaceOverBad X)
      (nativeFPlaceOverBad_mem_bad X))⟩

/-- The actual q candidate from the native clause (b) witness. -/
noncomputable def nativeQActual :
    NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  (nativeQDonorActual X).witness.parameter

/-- The actual q candidate from the source Tate comparison. -/
noncomputable def nativeQ (D : NativeQDonor X) :
    NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  D.witness.parameter


/-- Actual q-unit in the F-completion from the native Clause (b) q. -/
noncomputable def nativeQUnitActual :
    (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))ˣ :=
  Units.mk0 (nativeQActual X).q (nativeQActual X).q_ne_zero

/-- Actual q-unit in the algebraic closure of the completion. -/
noncomputable def nativeQUnitAlgClosedActual :
    (AlgebraicClosure (NumberFieldFinitePlace.Completion
      (nativeFPlaceOverBad X)))ˣ :=
  unitToAlgClosed (nativeQUnitActual X)

/-- Actual root system of the native q in the algebraic closure. -/
noncomputable def nativeRootsActual :
    NatRootSystem (nativeQUnitAlgClosedActual X) :=
  algClosedRootSystem (nativeQUnitActual X)

/-- Actual Kummer class tower from the native q root system. -/
noncomputable def nativeKummerClassActual :
    CyclotomicTower (AlgebraicClosure (NumberFieldFinitePlace.Completion
      (nativeFPlaceOverBad X))) :=
  KummerClass.rootSystemDiff (nativeRootsActual X) (nativeRootsActual X)

/-- The actual q-unit in the F-completion. -/
noncomputable def nativeQUnit (D : NativeQDonor X) :
    (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))ˣ :=
  Units.mk0 (nativeQ X D).q (nativeQ X D).q_ne_zero

/-- The actual q-unit mapped to the algebraic closure. -/
noncomputable def nativeQUnitAlgClosed (D : NativeQDonor X) :
    (AlgebraicClosure (NumberFieldFinitePlace.Completion
      (nativeFPlaceOverBad X)))ˣ :=
  unitToAlgClosed (nativeQUnit X D)

/-- The actual root system of q in the algebraic closure. -/
noncomputable def nativeRoots (D : NativeQDonor X) :
    NatRootSystem (nativeQUnitAlgClosed X D) :=
  algClosedRootSystem (nativeQUnit X D)

/-- The actual Kummer class tower, constructed as the root-system difference. -/
noncomputable def nativeKummerClass (D : NativeQDonor X) :
    CyclotomicTower (AlgebraicClosure (NumberFieldFinitePlace.Completion
      (K := X.S.arithmetic.F) (nativeFPlaceOverBad X))) :=
  KummerClass.rootSystemDiff (nativeRoots X D) (nativeRoots X D)

/-- Exact missing production declaration: actual tensor landing data from the
F-completion to the arithmetic tensor tuple block.  No such map exists in the
current tree. -/
structure NativeTensorLandingDonor where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type v
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type w
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X) → ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : ∀ (D : NativeQDonor X),
    tensorLanding (nativeQ X D).q = (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] NativeTensorLandingDonor.hp
attribute [instance] NativeTensorLandingDonor.tensorFintype

/-- Conditional actual native C3 data: q, roots, Kummer class, and tensor
landing, all from explicit actual donors. -/
structure NativeC3Data (D : NativeQDonor X) (L : NativeTensorLandingDonor X) where
  q : NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) := nativeQ X D
  qUnit : (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))ˣ :=
    nativeQUnit X D
  qUnit_eq : nativeQUnit X D = Units.mk0 (nativeQ X D).q (nativeQ X D).q_ne_zero := rfl
  roots : NatRootSystem (nativeQUnitAlgClosed X D) := nativeRoots X D
  kummerClass : CyclotomicTower (AlgebraicClosure (NumberFieldFinitePlace.Completion
    (nativeFPlaceOverBad X))) := nativeKummerClass X D
  tensorUnit : (ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple)ˣ := L.tensorUnit
  tensorLanding : NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X) →
    ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple := L.tensorLanding
  tensorLanding_q : L.tensorLanding (nativeQ X D).q =
    (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) :=
    L.tensorLanding_q D

/-- Zero-sorry conditional construction of the native C3 slice. -/
noncomputable def nativeC3DataOfDonors (D : NativeQDonor X)
    (L : NativeTensorLandingDonor X) : NativeC3Data X D L where
  q := nativeQ X D
  qUnit := nativeQUnit X D
  qUnit_eq := rfl
  roots := nativeRoots X D
  kummerClass := nativeKummerClass X D
  tensorUnit := L.tensorUnit
  tensorLanding := L.tensorLanding
  tensorLanding_q := L.tensorLanding_q D

theorem nativeTensorLandingDonor_nonempty (X : N8NativeInput l) :
    Nonempty (NativeTensorLandingDonor X) := by
  sorry

end LeanFormal.IUT.N8Closure.NativeC3
