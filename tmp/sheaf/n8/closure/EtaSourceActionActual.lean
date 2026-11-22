import tmp.sheaf.n8.closure.EtaRouteInterface
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# N8 source action actual

Constructs an actual action of the completion unit group on the native
log-shell carrier K by left multiplication, as ℚ-linear automorphisms, using
the actual nativeLocalShell K.  The action laws are proved.  The full
three-side chain equivariance of SourceLogShellXMuChainActionCompatibility
requires an actual chain supply D X F and is not constructed here; that is
the exact gap.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRouteInterface
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaSourceActionActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance nativeShellAlgebraRat : Algebra ℚ (NativeShell X).K :=
  inferInstanceAs (Algebra ℚ (CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (badPlaceAtPrime X)))

/-- Left multiplication by a completion unit as a ℚ-linear automorphism of K. -/
noncomputable def nativeMulLinearEquiv (u : (NativeShell X).Kˣ) :
    (NativeShell X).K ≃ₗ[ℚ] (NativeShell X).K where
  toFun x := (u : (NativeShell X).K) * x
  invFun x := (↑(u⁻¹) : (NativeShell X).K) * x
  left_inv x := by
    change (↑(u⁻¹) : (NativeShell X).K) * ((u : (NativeShell X).K) * x) = x
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    change (u : (NativeShell X).K) * ((↑(u⁻¹) : (NativeShell X).K) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by
    change (u : (NativeShell X).K) * (x + y) =
      (u : (NativeShell X).K) * x + (u : (NativeShell X).K) * y
    rw [mul_add]
  map_smul' c x := by
    change (u : (NativeShell X).K) * (c • x) = c • ((u : (NativeShell X).K) * x)
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc,
      mul_comm (u : (NativeShell X).K), mul_assoc]

/-- Actual source action: the completion unit group acts by left multiplication. -/
noncomputable def nativeSourceAction :
    (NativeShell X).Kˣ →* ((NativeShell X).K ≃ₗ[ℚ] (NativeShell X).K) where
  toFun := nativeMulLinearEquiv (X := X)
  map_one' := by
    ext x
    change (1 : (NativeShell X).K) * x = x
    rw [one_mul]
  map_mul' u v := by
    ext x
    change ((u * v : (NativeShell X).Kˣ) : (NativeShell X).K) * x =
      (u : (NativeShell X).K) * ((v : (NativeShell X).K) * x)
    rw [Units.val_mul, mul_assoc]

theorem nativeSourceAction_one :
    nativeSourceAction (X := X) 1 = 1 :=
  map_one (nativeSourceAction (X := X))

theorem nativeSourceAction_mul (u v : (NativeShell X).Kˣ) :
    nativeSourceAction (X := X) (u * v) =
      nativeSourceAction (X := X) u * nativeSourceAction (X := X) v :=
  map_mul (nativeSourceAction (X := X)) u v

/-- Actual N8 source-action package.  Group and action are actual; no free map. -/
structure N8SourceAction where
  group : Type u
  [groupInst : Group group]
  action : group →* ((NativeShell X).K ≃ₗ[ℚ] (NativeShell X).K)

attribute [instance] N8SourceAction.groupInst

noncomputable def n8SourceAction : N8SourceAction (X := X) where
  group := (NativeShell X).Kˣ
  action := nativeSourceAction (X := X)

/-- The action laws hold for the actual N8 source action. -/
theorem n8SourceAction_laws :
    (n8SourceAction (X := X)).action 1 = 1 ∧
      ∀ u v, (n8SourceAction (X := X)).action (u * v) =
        (n8SourceAction (X := X)).action u *
          (n8SourceAction (X := X)).action v :=
  ⟨map_one (nativeSourceAction (X := X)),
   fun u v => map_mul (nativeSourceAction (X := X)) u v⟩

end LeanFormal.IUT.N8Closure.EtaSourceActionActual

end