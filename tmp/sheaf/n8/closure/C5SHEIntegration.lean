import tmp.sheaf.n8.closure.C5DonorProof
import tmp.sheaf.n8.closure.C5Native

noncomputable section

namespace LeanFormal.IUT.N8Closure.C5SHEIntegration

universe ua uv upi umon ui uG

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.C5Native
open LeanFormal.IUT.N8Closure.C5DonorProof
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-- Actual-link SHE representation: the square uses the actual
`I.fLinkAt 0 0 0 0` links, not identity links. -/
abbrev SHERepresentationActual (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :=
  NativeSHEActual (l := l) (V := V) I

/-- New C5 target slice with the actual-link SHE field.  This is a precise
replacement target; the old `SHERepresentation` type is unchanged. -/
structure SourceAlgorithmCompatibilityDataActualSHE
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  iplFamily : IPLFamilyData I
  sheActual : SHERepresentationActual (l := l) (V := V) I

/-- The actual-SHE slice is inhabited from the native slices; APT/permitted are
not included in this slice. -/
noncomputable def actualSHESlice :
    SourceAlgorithmCompatibilityDataActualSHE I C1 C2 C3 C4 where
  iplFamily := nativeIPLFamily (l := l) (V := V) I
  sheActual := nativeSHEActual (l := l) (V := V) I

theorem actualSHESlice_nonempty :
    Nonempty (SourceAlgorithmCompatibilityDataActualSHE I C1 C2 C3 C4) :=
  ⟨actualSHESlice (l := l) (V := V) I C1 C2 C3 C4⟩

/-- Comparison of the old C5 SHE field with the actual-link SHE field.  Both
fields are retained; the old field is not reinterpreted as the actual one. -/
structure SHEOldActualComparison (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  old : SHERepresentation I
  actual : SHERepresentationActual (l := l) (V := V) I

theorem sheOldActualComparison_nonempty_iff :
    Nonempty (SHEOldActualComparison (l := l) (V := V) I) ↔
      Nonempty (SHERepresentation I) ∧
        Nonempty (SHERepresentationActual (l := l) (V := V) I) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨⟨C.old⟩, ⟨C.actual⟩⟩
  · rintro ⟨⟨old⟩, ⟨actual⟩⟩
    exact ⟨{ old := old, actual := actual }⟩

/-- Full target with the new actual-SHE field; APT and permitted remain the
exact missing components.  This is a decomposition/no-go, not an inhabitant. -/
structure SourceAlgorithmCompatibilityDataActualSHEFull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  iplFamily : IPLFamilyData I
  sheActual : SHERepresentationActual (l := l) (V := V) I
  aptMissing : NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4
  permittedMissing : NativePermittedActual l

theorem sourceAlgorithmCompatibilityDataActualSHEFull_nonempty_iff :
    Nonempty (SourceAlgorithmCompatibilityDataActualSHEFull I C1 C2 C3 C4) ↔
      Nonempty (IPLFamilyData I) ∧
        Nonempty (SHERepresentationActual (l := l) (V := V) I) ∧
          Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) ∧
            Nonempty (NativePermittedActual l) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨D.iplFamily⟩, ⟨D.sheActual⟩, ⟨D.aptMissing⟩, ⟨D.permittedMissing⟩⟩
  · rintro ⟨⟨ipl⟩, ⟨she⟩, ⟨apt⟩, ⟨perm⟩⟩
    exact ⟨{ iplFamily := ipl, sheActual := she, aptMissing := apt, permittedMissing := perm }⟩

end LeanFormal.IUT.N8Closure.C5SHEIntegration
