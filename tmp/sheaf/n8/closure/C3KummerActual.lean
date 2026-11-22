import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTII.Kummer.KummerClass
import Mathlib

/-!
# C3 actual Kummer class and root change

Starting from the native actual q-unit and the algebraic-closure roots in
NativeC3, this file constructs the actual Kummer class from a source Galois
action and the actual root-change tower from two actual root systems.

No CyclotomicTower is introduced as a free field: every tower below is built by
KummerClass.kummerClass or KummerClass.rootSystemDiff.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C3KummerActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Roots

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l) (D : NativeQDonor X)

/-- The actual field whose units carry the Kummer class. -/
abbrev nativeKummerField : Type :=
  AlgebraicClosure (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))

/-- The actual value unit: the native q-unit in the algebraic closure. -/
abbrev nativeValue : (nativeKummerField X)ˣ :=
  nativeQUnitAlgClosed X D

/-- The actual algebraic-closure root system from NativeC3. -/
abbrev nativeValueRoots : NatRootSystem (nativeValue X D) :=
  nativeRoots X D

/-- Source Galois action on the algebraic closure units, with the actual fixed
q-unit property.  This is source data, not a free tower. -/
structure NativeKummerAction where
  G : Type u
  [groupG : Group G]
  rho : G →* ((nativeKummerField X)ˣ ≃* (nativeKummerField X)ˣ)
  fixed : ∀ σ : G, rho σ (nativeValue X D) = nativeValue X D

attribute [instance] NativeKummerAction.groupG

/-- The actual Kummer class at a source Galois element. -/
noncomputable def nativeKummerClass (A : NativeKummerAction X D) (σ : A.G) :
    CyclotomicTower (nativeKummerField X) :=
  KummerClass.kummerClass A.rho (nativeValueRoots X D) A.fixed σ

/-- The actual Kummer class is trivial at the identity. -/
theorem nativeKummerClass_one (A : NativeKummerAction X D) :
    nativeKummerClass X D A 1 = CyclotomicTower.one :=
  KummerClass.kummerClass_one A.rho (nativeValueRoots X D) A.fixed

/-- The actual crossed Kummer class multiplication law. -/
theorem nativeKummerClass_mul (A : NativeKummerAction X D) (σ τ : A.G) :
    nativeKummerClass X D A (σ * τ) =
      CyclotomicTower.mul
        (KummerClass.action A.rho σ (nativeKummerClass X D A τ))
        (nativeKummerClass X D A σ) :=
  KummerClass.kummerClass_mul A.rho (nativeValueRoots X D) A.fixed σ τ

/-- The actual root-change tower attached to two actual root systems of the
same value. -/
noncomputable def nativeRootChange (first second : NatRootSystem (nativeValue X D)) :
    CyclotomicTower (nativeKummerField X) :=
  KummerClass.rootSystemDiff first second

/-- The actual change-of-root coboundary identity for the native Kummer class. -/
theorem nativeRootChange_kummerClass_diff (A : NativeKummerAction X D)
    (first second : NatRootSystem (nativeValue X D)) (σ : A.G) :
    CyclotomicTower.mul
        (KummerClass.kummerClass A.rho second A.fixed σ)
        (nativeRootChange X D first second) =
      CyclotomicTower.mul
        (KummerClass.kummerClass A.rho first A.fixed σ)
        (KummerClass.action A.rho σ (nativeRootChange X D first second)) :=
  KummerClass.kummerClass_diff A.rho A.fixed first second σ

/-- The native root-change of the actual roots with themselves is the
root-system-difference tower (not an arbitrary field). -/
theorem nativeRootChange_self :
    nativeRootChange X D (nativeValueRoots X D) (nativeValueRoots X D) =
      CyclotomicTower.one := by
  -- rootSystemDiff of equal systems has component 1 for every n; this is the
  -- actual zero-change identity, not a free tower assignment.
  apply CyclotomicTower.ext
  intro n
  simp [nativeRootChange, KummerClass.rootSystemDiff, CyclotomicTower.one]

end LeanFormal.IUT.N8Closure.C3KummerActual
