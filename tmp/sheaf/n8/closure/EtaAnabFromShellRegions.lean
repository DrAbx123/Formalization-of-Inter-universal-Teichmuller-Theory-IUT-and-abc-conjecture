import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison
import tmp.sheaf.n8.closure.EtaKummerSourceDatumAtF
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import tmp.sheaf.n8.closure.EtaSourceActionConcrete
import tmp.sheaf.n8.closure.EtaAnabToVaryingRss
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmOpenMap
import Mathlib

/-!
# etaAnab from actual F-place shell regions

Target correction: the function-valued ThetaPilotPoint is not used to extract
K-regions.  This file builds the actual positive finite region from the F-place
shell

  fSourceDatum X = fPlaceShell X = sourceLocalLogShellDatum at nativeFPlaceAtPrime

and the production integralLogShell.  It then reads the varying-Rss class of
that region and proves Kummer-image compatibility and the C4 action laws.

No toK bridge and no arbitrary region are introduced.
-/

noncomputable section

namespace ABCBridge.N8.EtaAnabFromShellRegions

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.EtaKummerSourceDatumAtF
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open ABCBridge.N8.EtaSourceActionConcrete
open ABCBridge.N8.C3TensorTargetCorrection
open ABCBridge.N8.EtaAnabToVaryingRss
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.LocalFieldLogarithm
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable {C4 : SourceWitnessedOutputData (l := l) (V := V) I Label}
variable {X : N8NativeInput l}
variable {n : ThetaPilotCarrier l}
variable {x : I.ThetaPilotPoint C4.place.v}

/-- The actual F-place completion. -/
abbrev FPlaceK (X : N8NativeInput l) : Type := FPlaceCompletion X

local instance fPlaceMeasurableSpace (X : N8NativeInput l) : MeasurableSpace (FPlaceK X) :=
  borel (FPlaceK X)

local instance fPlaceBorelSpace (X : N8NativeInput l) : BorelSpace (FPlaceK X) :=
  ⟨rfl⟩

/-- Actual Haar measure on the F-place completion. -/
noncomputable abbrev fPlaceMeasure (X : N8NativeInput l) : Measure (FPlaceK X) :=
  Measure.addHaar

/-- The actual F-place shell equals the production integralLogShell. -/
theorem fSourceDatum_logShell_eq_integral :
    (fSourceDatum X).logShell =
      (integralLogShell (K := FPlaceK X)
        (p := nativePrime X) : Set (FPlaceK X)) :=
  sourceLocalLogShellDatum_logShell_eq_integralLogShell
    (K := X.S.arithmetic.F) (p := nativePrime X)
    (nativeFPlaceAtPrime X)

/-- Actual positive finite region from the F-place shell. -/
noncomputable def fPlaceShellRegion :
    PositiveFiniteRegion (FPlaceK X) (fPlaceMeasure X) where
  carrier := (fSourceDatum X).logShell
  measurable := by
    rw [fSourceDatum_logShell_eq_integral]
    exact (isOpen_integralLogShell (K := FPlaceK X)
      (p := nativePrime X)).measurableSet
  pos := by
    rw [fSourceDatum_logShell_eq_integral]
    exact (measure_integralLogShell_pos_lt_top (K := FPlaceK X)
      (p := nativePrime X) (fPlaceMeasure X)).1
  finite := by
    rw [fSourceDatum_logShell_eq_integral]
    exact (measure_integralLogShell_pos_lt_top (K := FPlaceK X)
      (p := nativePrime X) (fPlaceMeasure X)).2

/-- The actual varying-Rss class of the F-place shell region. -/
noncomputable def fPlaceShellClass :
    Rss (K := FPlaceK X) (fPlaceMeasure X) :=
  regionClass (K := FPlaceK X) (mu := fPlaceMeasure X) (fPlaceShellRegion (X := X))

/-- Actual Kummer-image compatibility: every Kummer image lies in the shell
region carrier. -/
theorem fPlaceShellRegion_kummer_mem
    (u : (fSourceDatum X).Units) :
    ((fSourceDatum X).logMap u).toAdd ∈ (fPlaceShellRegion (X := X)).carrier := by
  exact fSourceDatum_codomainKummerContained X ⟨u, rfl⟩

/-- Actual etaAnab shell-region package, compatible with the concrete source
action: the F-place shell region, its varying-Rss class, Kummer membership, and
the actual Ind1/Ind2/Ind3 laws. -/
structure EtaAnabFromShellRegionsData
    (A : EtaSourceActionConcrete C4 X n x) where
  region : PositiveFiniteRegion (FPlaceK X) (fPlaceMeasure X) :=
    fPlaceShellRegion (X := X)
  rssClass : Rss (K := FPlaceK X) (fPlaceMeasure X) :=
    fPlaceShellClass (X := X)
  kummer_mem : ∀ u : (fSourceDatum X).Units,
    ((fSourceDatum X).logMap u).toAdd ∈ region.carrier
  ind1 : Label →* Equiv.Perm (I.ThetaPilotPoint C4.place.v) := A.ind1
  ind2 : Label →* Equiv.Perm (I.ThetaPilotPoint C4.place.v) := A.ind2
  ind3_nonarch : Nat → Set (I.ThetaPilotPoint C4.place.v) →
    Set (I.ThetaPilotPoint C4.place.v) := A.ind3_nonarch
  ind3_arch : Nat → Set (I.ThetaPilotPoint C4.place.v) →
    Set (I.ThetaPilotPoint C4.place.v) := A.ind3_arch


/-- Actual shell-region etaAnab package from the concrete source action. -/
noncomputable def etaAnabFromShellRegionsData
    (A : EtaSourceActionConcrete C4 X n x) :
    EtaAnabFromShellRegionsData (X := X) A where
  region := fPlaceShellRegion (X := X)
  rssClass := fPlaceShellClass (X := X)
  kummer_mem := fun u => fPlaceShellRegion_kummer_mem (X := X) u
  ind1 := A.ind1
  ind2 := A.ind2
  ind3_nonarch := A.ind3_nonarch
  ind3_arch := A.ind3_arch

/-- Actual Ind3 nonarchimedean one-way control at the shell-region level. -/
theorem etaAnabFromShellRegionsData_ind3_nonarch
    (A : EtaSourceActionConcrete C4 X n x) (m : Nat)
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    S ⊆ A.ind3_nonarch m S :=
  A.ind3_nonarch_inclusion m S

/-- Actual Ind3 archimedean one-way control at the shell-region level. -/
theorem etaAnabFromShellRegionsData_ind3_arch
    (A : EtaSourceActionConcrete C4 X n x) (m : Nat)
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    A.ind3_arch m S ⊆ S :=
  A.ind3_arch_surjection m S

end ABCBridge.N8.EtaAnabFromShellRegions
