import tmp.sheaf.n8.closure.C1ActualDataNative
import tmp.sheaf.n8.closure.C6ConstructedBridge

/-! # C1 actual data from the C6 donor supplies

This file composes the C6 donor constructors with the native C1-data
construction: a contract supply over the native arithmetic root, a family
index equivalence, a selected realization R and a prime-strip fiber
comparison F produce an actual `C1ActualData` and `SourceInputBinding`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C6ConstructedBridge
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable (h : C6ContractSupply X)
variable (e : X.family.index ≃ SourceTheorem311Index)

/-- The old input determined by the C6 contract/index donors. -/
abbrev nativeC6Input : OriginalInput l (NativePlaces X.S) :=
  nativeOriginalInputOfDonors X (nativeOriginalInputDonorsOf X h e)

/-- Actual C1 data from the C6 contract/index donors plus R and F. -/
noncomputable def c1ActualDataOfC6Supplies
    (R : nativeC6Input X h e |>.SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeC6Input X h e).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := (nativeOriginalInputDonorsOf X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonorsOf X h e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    C1ActualData (nativeC6Input X h e) :=
  c1ActualDataOfNativeDonors X (nativeOriginalInputDonorsOf X h e)
    (nativePlaceBindingDonorsOf X (nativeC6Input X h e)
      (nativeOriginalInputDonorsOf X h e).initial_arithmetic R F)

/-- Actual SourceInputBinding from the C6 donor supplies. -/
noncomputable def sourceInputBindingOfC6Supplies
    (R : nativeC6Input X h e |>.SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeC6Input X h e).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := (nativeOriginalInputDonorsOf X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonorsOf X h e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    SourceInputBinding (nativeC6Input X h e) :=
  sourceInputBindingOfActual (nativeC6Input X h e)
    (c1ActualDataOfC6Supplies X h e R F)

theorem sourceInputBinding_nonempty_of_c6Supplies
    (R : nativeC6Input X h e |>.SourceImageRealization (badPlace X))
    (F : ∀ (n m : Int) (v : NativePlaces X.S),
      ((nativeC6Input X h e).primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := (nativeOriginalInputDonorsOf X h e).initial.arithmetic.Fmod)
          (((nativeOriginalInputDonorsOf X h e).initial_arithmetic ▸ nativePlaceIndexEquiv X) v)) :
    Nonempty (SourceInputBinding (nativeC6Input X h e)) :=
  ⟨sourceInputBindingOfC6Supplies X h e R F⟩

end LeanFormal.IUT.N8Closure.C1Actual