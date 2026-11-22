import tmp.sheaf.n8.closure.C3TensorTargetCorrection
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import Mathlib

/-!
# etaAnab at the native F-place

Carrier correction: the native q and etaQ live in the F-completion at
`NativeC3.nativeFPlaceOverBad`, not in the Fmod base shell.  This file uses the
actual F-place `sourceLocalLogShellDatum` and its production log-shell volume
consumer.  Fmod and F layers are not mixed.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume

namespace LeanFormal.IUT.N8Closure.EtaAnabAtFPlace

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The rational prime under the actual native F-place. -/
noncomputable abbrev FPlacePrime : ℕ :=
  (NumberFieldFinitePlace.completionRationalPrime (nativeFPlaceOverBad X)).val

local instance FPlacePrimeFact : Fact (Nat.Prime (FPlacePrime X)) :=
  ⟨(NumberFieldFinitePlace.completionRationalPrime (nativeFPlaceOverBad X)).2⟩

/-- The actual native F-place as a prime-indexed finite place. -/
noncomputable def nativeFPlaceAtPrime :
    FinitePlaceAtPrime X.S.arithmetic.F (FPlacePrime X) :=
  ⟨nativeFPlaceOverBad X, rfl⟩

/-- Actual source log-shell at the F-completion. -/
noncomputable def localShellAtF : SourceLogShellDatum :=
  sourceLocalLogShellDatum (K := X.S.arithmetic.F) (p := FPlacePrime X)
    (nativeFPlaceAtPrime X)

/-- Actual F-completion log-shell integral structure. -/
def integralStructureAtF : Set (CommonPrimeCompletion
    (K := X.S.arithmetic.F) (nativeFPlaceAtPrime X)) :=
  (localShellAtF X).logShell

theorem integralStructureAtF_eq :
    integralStructureAtF X = (localShellAtF X).logShell := rfl

/-- Actual log-shell volume consumer at the F-place. -/
noncomputable def volumeConsumerAtF :
    LogShellVolumeConsumer (K := CommonPrimeCompletion
      (K := X.S.arithmetic.F) (nativeFPlaceAtPrime X)) (p := FPlacePrime X) :=
  logShellVolumeConsumer (K := CommonPrimeCompletion
    (K := X.S.arithmetic.F) (nativeFPlaceAtPrime X)) (p := FPlacePrime X)

/-- Actual etaAnab Rss at the F-place: F log-shell subset, volume index and
real log-volume coordinate. -/
structure EtaRssAtFPlace where
  shell : Set (CommonPrimeCompletion (K := X.S.arithmetic.F)
    (nativeFPlaceAtPrime X))
  shell_eq : shell = (localShellAtF X).logShell
  volumeIndex : ℕ
  volumeIndex_eq : volumeIndex = (volumeConsumerAtF X).index
  logVolume : ℝ
  logVolume_eq : logVolume = Real.log (volumeIndex : ℝ)

/-- Actual F-place Rss construction. -/
noncomputable def etaRssAtFPlace : EtaRssAtFPlace X where
  shell := (localShellAtF X).logShell
  shell_eq := rfl
  volumeIndex := (volumeConsumerAtF X).index
  volumeIndex_eq := rfl
  logVolume := Real.log ((volumeConsumerAtF X).index : ℝ)
  logVolume_eq := rfl

/-- Actual Rss carrier at the F-place, not the bare real line. -/
abbrev RssAtF : Type := EtaRssAtFPlace X

/-- Exact Ind handling labels at the F-place; Ind1 integral structure, Ind2
Kummer vertical, Ind3 upper-semi.  No free Real adjustment. -/
inductive IndAtFPlace
  | ind1_integral_structure
  | ind2_kummer_vertical
  | ind3_upper_semi
  deriving DecidableEq, Repr

def indAtFPlace : List IndAtFPlace :=
  [.ind1_integral_structure, .ind2_kummer_vertical, .ind3_upper_semi]

theorem indAtFPlace_length : (indAtFPlace).length = 3 := rfl

/-- Ind3 exact upper-semi from the production vertical log-Kummer contract. -/
def ind3UpperSemiAtF (K : VerticalLogKummerCorrespondence)
    (x₀ : K.F 0) (hull : K.D) : Prop :=
  K.HullDominates x₀ hull

/-- Exact missing Kummer vertical actual construction at the F-place. -/
def kummerVerticalAtFActual : Prop :=
  Nonempty (VerticalLogKummerCorrespondence.{u, u})

end LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
