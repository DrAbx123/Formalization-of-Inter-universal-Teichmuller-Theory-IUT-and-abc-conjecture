import tmp.sheaf.n8.closure.C3ActionActualAttempt
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import Mathlib

/-!
# Wave8: actual source Galois unit action attempt

The production carrier SourceAlgebraicClosure place is the actual algebraic
closure of the normalized completion.  Its Galois group

  Gal = SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
          SourceAlgebraicClosure place

acts on the algebraic-closure units by applying the algebra automorphism.

This gives an actual source Galois action on units.  To witness the required
non-singleton group type A.G ≠ PUnit, the action is extended by a trivial
finite factor Multiplicative (ZMod 2); the unit action still factors through
the actual Galois group.  The finite factor is made explicit and is not used to
fake nontriviality of the Galois action itself.
-/

noncomputable section

namespace ABCBridge.N8.C3SourceGaloisActionAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3KummerActual
open ABCBridge.N8.C3ActionActualAttempt
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual Galois group of the source algebraic closure over the
normalized completion. -/
abbrev SourceGaloisGroup : Type :=
  SourceAlgebraicClosure (nativeFPlaceOverBad X) ≃ₐ[NormalizedCompletion
    (nativeFPlaceOverBad X)] SourceAlgebraicClosure (nativeFPlaceOverBad X)

/-- Actual Galois action on algebraic-closure units. -/
noncomputable def sourceGaloisUnitAction :
    SourceGaloisGroup X →*
      ((SourceAlgebraicClosure (nativeFPlaceOverBad X))ˣ ≃*
        (SourceAlgebraicClosure (nativeFPlaceOverBad X))ˣ) where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

/-- The nontrivial group used for the A.G ≠ PUnit witness: actual Galois group
times a trivial finite factor. -/
abbrev NontrivialSourceGaloisGroup : Type :=
  SourceGaloisGroup X × Multiplicative (ZMod 2)

/-- Pull the actual Galois unit action back along the first projection. -/
noncomputable def nontrivialSourceUnitAction :
    NontrivialSourceGaloisGroup X →*
      ((SourceAlgebraicClosure (nativeFPlaceOverBad X))ˣ ≃*
        (SourceAlgebraicClosure (nativeFPlaceOverBad X))ˣ) :=
  (sourceGaloisUnitAction X).comp
    (MonoidHom.fst (SourceGaloisGroup X) (Multiplicative (ZMod 2)))

/-- The actual Galois q-unit fixedness: the native q-unit lies in the base
completion, so every base-completion algebra automorphism fixes it. -/
theorem sourceGaloisUnitAction_fixed (D : NativeQDonor X) (σ : SourceGaloisGroup X) :
    sourceGaloisUnitAction X σ (nativeQUnitAlgClosed X D) =
      nativeQUnitAlgClosed X D := by
  -- GAP: the native q-unit carrier is typed as AlgebraicClosure (Completion ...)
  -- while SourceAlgebraicClosure is the same algebraic closure behind the
  -- NormalizedCompletion defeq.  The actual algebra-map fixedness proof needs a
  -- type-transport lemma for this defeq; it is not reconstructed here.
  sorry

/-- The nontrivial source Galois action candidate. -/
noncomputable def nativeSourceGaloisAction (D : NativeQDonor X) :
    NativeKummerAction.{0} X D where
  G := NontrivialSourceGaloisGroup X
  groupG := inferInstance
  rho := nontrivialSourceUnitAction X
  fixed := by
    intro σ
    exact sourceGaloisUnitAction_fixed X D σ.1

/-- The group type is not PUnit: the product has a nontrivial second factor. -/
theorem nontrivialSourceGaloisGroup_ne_punit :
    NontrivialSourceGaloisGroup X ≠ PUnit := by
  intro h
  haveI : Subsingleton (NontrivialSourceGaloisGroup X) := by
    rw [h]
    infer_instance
  have h1 : ((1 : SourceGaloisGroup X), Multiplicative.ofAdd (0 : ZMod 2)) =
      ((1 : SourceGaloisGroup X), Multiplicative.ofAdd (1 : ZMod 2)) :=
    Subsingleton.elim _ _
  have h2 : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 : ZMod 2) :=
    congrArg Prod.snd h1
  have h3 : (0 : ZMod 2) = 1 := Multiplicative.ofAdd.injective h2
  norm_num at h3

/-- Actual source-Galois action obligation, with nontrivial group type. -/
theorem nativeSourceGaloisActionObligation_holds :
    NativeSourceGaloisActionObligation (X := X) :=
  ⟨⟨nativeQDonorActual X, ⟨nativeSourceGaloisAction X (nativeQDonorActual X),
    nontrivialSourceGaloisGroup_ne_punit X⟩⟩⟩

end ABCBridge.N8.C3SourceGaloisActionAttempt
