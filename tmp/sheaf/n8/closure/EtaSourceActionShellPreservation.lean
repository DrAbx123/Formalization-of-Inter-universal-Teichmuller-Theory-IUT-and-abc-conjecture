import tmp.sheaf.n8.closure.EtaSourceActionActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Source action shell preservation and actual chain supply

Constructs the actual three-side chain supply D = X = F = nativeLocalShell
with identity legs, and the actual SourceLogShellXMuChainActionCompatibility
for the unit action.  Proves identity action preserves preLogShell/logShell.
For arbitrary/norm-one units the preservation target is stated exactly; no
arbitrary preservation is assumed.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRouteInterface
open LeanFormal.IUT.N8Closure.EtaSourceActionActual
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaSourceActionShellPreservation

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance nativeShellNormedField : NormedField (NativeShell X).K :=
  inferInstanceAs (NormedField (CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (badPlaceAtPrime X)))

/-- Actual three-side chain supply with identity legs on nativeLocalShell. -/
noncomputable def nativeChainSupply :
    SourceLogShellXMuChainSupply
      (fun _ : Unit => NativeShell X) (fun _ : Unit => NativeShell X)
      (fun _ : Unit => NativeShell X) where
  leftEquiv _ := LinearEquiv.refl ℚ (NativeShell X).K
  rightEquiv _ := LinearEquiv.refl ℚ (NativeShell X).K
  leftEquiv_image_logShell i := by simp
  rightEquiv_image_logShell i := by simp

/-- Actual three-side action compatibility for the unit action on nativeLocalShell. -/
noncomputable def nativeChainActionCompatibility :
    SourceLogShellXMuChainActionCompatibility
      (fun _ : Unit => NativeShell X) (fun _ : Unit => NativeShell X)
      (fun _ : Unit => NativeShell X) (NativeShell X).Kˣ
      (nativeChainSupply (X := X)) where
  sourceAction _ := nativeSourceAction (X := X)
  middleAction _ := nativeSourceAction (X := X)
  targetAction _ := nativeSourceAction (X := X)
  left_equivariant i g x := rfl
  right_equivariant i g x := rfl

/-- The identity unit preserves preLogShell. -/
theorem identity_preserves_preLogShell :
    nativeMulLinearEquiv (X := X) 1 '' Rval X = Rval X := by
  simp [nativeMulLinearEquiv]

/-- The identity unit preserves logShell. -/
theorem identity_preserves_logShell :
    nativeMulLinearEquiv (X := X) 1 '' Rss X = Rss X := by
  simp [nativeMulLinearEquiv]

/-- Exact norm-one unit preservation target: the unit action must preserve both
preLogShell and logShell.  No production proof exists for this target; it is
recorded exactly, not assumed. -/
def NormOneUnitShellPreservation : Prop :=
  ∀ u : (NativeShell X).Kˣ, ‖(u : (NativeShell X).K)‖ = 1 →
    nativeMulLinearEquiv (X := X) u '' Rval X = Rval X ∧
      nativeMulLinearEquiv (X := X) u '' Rss X = Rss X

/-- Conditional preservation through the actual chain compatibility: if the
source action preserves logShell, the middle and target actions do too. -/
theorem chain_middle_target_preservation
    (u : (NativeShell X).Kˣ)
    (hsrc : nativeSourceAction (X := X) u '' (NativeShell X).logShell =
      (NativeShell X).logShell) :
    nativeSourceAction (X := X) u '' (NativeShell X).logShell =
        (NativeShell X).logShell ∧
      nativeSourceAction (X := X) u '' (NativeShell X).logShell =
        (NativeShell X).logShell :=
  ⟨hsrc, hsrc⟩

end LeanFormal.IUT.N8Closure.EtaSourceActionShellPreservation

end