import tmp.sheaf.n8.closure.C5APTProof
import tmp.sheaf.n8.closure.P6SHEInd

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6APTActual

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
open LeanFormal.IUT.N8Closure.C5SHEIntegration
open LeanFormal.IUT.N8Closure.C5APTProof
open LeanFormal.IUT.N8Closure.P6SHEInd
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Wave2 APT actual / exact no-go -/

/-- The only actual production one-column structure is tied to
`NumberField.FinitePlace k`; it is not an inhabitant for arbitrary C5 `V`. -/
noncomputable def productionOneColumnAtFinitePlaces (k : Type) [Field k] [NumberField k] :
    SourceOneColumnArithmeticHolomorphicStructure (NumberField.FinitePlace k) :=
  sourceOneColumnStructureOfNumberField k

/-- Exact no-go for the APT slice: the three actual fields are precisely what
is missing; no production inhabitant currently exists. -/
theorem p6NativeAPTMissing_exactNoGo :
    Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) ↔
      ∃ S : SourceOneColumnArithmeticHolomorphicStructure V,
        ∃ A : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
          (Multiplicative LAdd) I 0 (I.ThetaPilotPoint C4.place.v),
          Nonempty (SourceAlgorithmicParallelTransport S A A) :=
  nativeAPTMissing_exactNoGo (I := I) (C4 := C4)

/-- Exact missing APT fields, exposed one by one (no free Prop). -/
structure P6APTMissingFields where
  missingS : SourceOneColumnArithmeticHolomorphicStructure V
  missingA : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
    (Multiplicative LAdd) I 0 (I.ThetaPilotPoint C4.place.v)
  missingTransport : SourceAlgorithmicParallelTransport missingS missingA missingA

theorem p6APTMissingFields_nonempty_iff :
    Nonempty (P6APTMissingFields (l := l) (V := V) I (LAdd := LAdd) C4) ↔
      Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨{ missingOneColumn := F.missingS, missingAlgorithm := F.missingA, missingTransport := F.missingTransport }⟩
  · rintro ⟨D⟩
    exact ⟨{ missingS := D.missingOneColumn, missingA := D.missingAlgorithm, missingTransport := D.missingTransport }⟩

/-! ## Permitted exact no-go -/

/-- The candidate label family and label `0` are actual signed-label data but
are not the source-constrained permitted family. -/
noncomputable def candidatePermitted : Set (SignedLabel l.value) := Set.univ
noncomputable def candidatePilot : SignedLabel l.value := ⟨0, by constructor <;> omega⟩
theorem candidatePilot_mem : candidatePilot (l := l) ∈ candidatePermitted (l := l) :=
  Set.mem_univ _

/-- Exact no-go for the permitted slice: a source-constrained family and its
selected member are still missing. -/
theorem p6NativePermittedActual_exactNoGo :
    Nonempty (NativePermittedActual l) ↔
      ∃ P : Set (SignedLabel l.value),
        ∃ j : SignedLabel l.value, P.Nonempty ∧ j ∈ P :=
  nativePermittedActual_exactNoGo

end LeanFormal.IUT.N8Closure.P6APTActual
