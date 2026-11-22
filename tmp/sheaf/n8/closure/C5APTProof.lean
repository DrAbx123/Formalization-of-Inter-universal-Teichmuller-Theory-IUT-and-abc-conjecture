import tmp.sheaf.n8.closure.C5SHEIntegration
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding

noncomputable section

namespace LeanFormal.IUT.N8Closure.C5APTProof

universe ua uv upi umon ui uG uL

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
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Production one-column donor

The only actual production one-column structure is over the finite places of a
number field.  It does not inhabit the arbitrary `V` slot of C5 directly; this
is part of the exact APT-S no-go. -/

noncomputable def productionOneColumnStructure (k : Type) [Field k] [NumberField k] :
    SourceOneColumnArithmeticHolomorphicStructure (NumberField.FinitePlace k) :=
  sourceOneColumnStructureOfNumberField k

/-! ## Native APT -/

/-- Exact no-go form: `NativeAPTMissing` is inhabited exactly when actual S/A/
transport are supplied.  No production instance of all three is in the tree. -/
theorem nativeAPTMissing_exactNoGo :
    Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) ↔
      ∃ S : SourceOneColumnArithmeticHolomorphicStructure V,
        ∃ A : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
          (Multiplicative LAdd) I 0 (I.ThetaPilotPoint C4.place.v),
          Nonempty (SourceAlgorithmicParallelTransport S A A) :=
  nativeAPTMissing_nonempty_iff (I := I) (C4 := C4)

/-- Conditional production route: supplying the three actual donors closes the
native APT slice; this is not an inhabitant. -/
theorem nativeAPTMissing_of_production
    (S : SourceOneColumnArithmeticHolomorphicStructure V)
    (A : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
      (Multiplicative LAdd) I 0 (I.ThetaPilotPoint C4.place.v))
    (transport : SourceAlgorithmicParallelTransport S A A) :
    Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) :=
  nativeAPTMissing_of_actual (l := l) (V := V) I (LAdd := LAdd) C4 S A transport

/-! ## Permitted family -/

/-- Actual signed-label type/data: the full candidate label set and the label
`0`.  This is a candidate family, not the source-constrained permitted family. -/
noncomputable def productionCandidateLabels : Set (SignedLabel l.value) :=
  Set.univ

noncomputable def productionCandidatePilot : SignedLabel l.value :=
  ⟨0, by constructor <;> omega⟩

theorem productionCandidatePilot_mem :
    productionCandidatePilot (l := l) ∈ productionCandidateLabels (l := l) :=
  Set.mem_univ _

/-- Exact no-go form for the permitted slice: a source-constrained family and
its selected member must be supplied; the candidate set is not claimed actual. -/
theorem nativePermittedActual_exactNoGo :
    Nonempty (NativePermittedActual l) ↔
      ∃ P : Set (SignedLabel l.value),
        ∃ j : SignedLabel l.value, P.Nonempty ∧ j ∈ P :=
  nativePermittedActual_nonempty_iff

/-! ## SHE actual-link integration -/

/-- The new SHE target uses the actual-link slice from C5SHEIntegration; no
identity-leg pretense is introduced here. -/
noncomputable def actualSHESliceWithAPTProof :
    SourceAlgorithmCompatibilityDataActualSHE I C1 C2 C3 C4 :=
  actualSHESlice (l := l) (V := V) I C1 C2 C3 C4

theorem actualSHESliceWithAPTProof_nonempty :
    Nonempty (SourceAlgorithmCompatibilityDataActualSHE I C1 C2 C3 C4) :=
  ⟨actualSHESliceWithAPTProof (l := l) (V := V) I C1 C2 C3 C4⟩

/-- Full actual-SHE target remains exactly the conjunction of IPL/actual SHE/
APT/permitted; APT and permitted are exact no-go components. -/
theorem actualSHEFull_exactNoGo :
    Nonempty (SourceAlgorithmCompatibilityDataActualSHEFull I C1 C2 C3 C4) ↔
      Nonempty (IPLFamilyData I) ∧
        Nonempty (SHERepresentationActual (l := l) (V := V) I) ∧
          Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) ∧
            Nonempty (NativePermittedActual l) :=
  sourceAlgorithmCompatibilityDataActualSHEFull_nonempty_iff (I := I) C1 C2 C3 C4

end LeanFormal.IUT.N8Closure.C5APTProof
