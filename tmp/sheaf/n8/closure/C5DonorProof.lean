import tmp.sheaf.n8.closure.C5Native

noncomputable section

namespace LeanFormal.IUT.N8Closure.C5DonorProof

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
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Native APT exact decomposition

`NativeAPTMissing` is nonempty exactly when an actual one-column structure,
an actual multradial algorithm on the C4 output, and an actual parallel
transport exist.  This is the exact no-go boundary; the gate structure
`SourceOneColumnArithmeticHolomorphicStructure.nonempty` is not used. -/

theorem nativeAPTMissing_nonempty_iff :
    Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) ↔
      ∃ S : SourceOneColumnArithmeticHolomorphicStructure V,
        ∃ A : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
          (Multiplicative LAdd) I 0 (I.ThetaPilotPoint C4.place.v),
          Nonempty (SourceAlgorithmicParallelTransport S A A) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.missingOneColumn, D.missingAlgorithm, ⟨D.missingTransport⟩⟩
  · rintro ⟨S, A, ⟨transport⟩⟩
    exact ⟨{ missingOneColumn := S, missingAlgorithm := A, missingTransport := transport }⟩

/-- Conditional constructor: actual APT data supply the native missing slice.
This is an interface implication, not an inhabitant of the target. -/
theorem nativeAPTMissing_of_actual
    (S : SourceOneColumnArithmeticHolomorphicStructure V)
    (A : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
      (Multiplicative LAdd) I 0 (I.ThetaPilotPoint C4.place.v))
    (transport : SourceAlgorithmicParallelTransport S A A) :
    Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) :=
  ⟨{ missingOneColumn := S, missingAlgorithm := A, missingTransport := transport }⟩

/-! ## Native permitted exact decomposition

`NativePermittedActual` is nonempty exactly when a nonempty permitted label set
and a selected member exist.  The candidate singleton family in C5Native is
not asserted as the source-constrained family. -/

theorem nativePermittedActual_nonempty_iff :
    Nonempty (NativePermittedActual l) ↔
      ∃ P : Set (SignedLabel l.value),
        ∃ j : SignedLabel l.value, P.Nonempty ∧ j ∈ P := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.permitted, D.pilotLabel, D.permitted_nonempty, D.pilotLabel_mem⟩
  · rintro ⟨P, j, hP, hj⟩
    exact ⟨{ permitted := P, pilotLabel := j, permitted_nonempty := hP, pilotLabel_mem := hj }⟩

/-- Conditional constructor: an actual permitted family supplies the native
missing slice. -/
theorem nativePermittedActual_of_actual
    (P : Set (SignedLabel l.value)) (j : SignedLabel l.value)
    (hP : P.Nonempty) (hj : j ∈ P) :
    Nonempty (NativePermittedActual l) :=
  ⟨{ permitted := P, pilotLabel := j, permitted_nonempty := hP, pilotLabel_mem := hj }⟩

/-! ## SHE type bridge

The actual-link SHE square is `NativeSHEActual I`; the C5 `SHERepresentation`
field is fixed to identity `FPrimeStripLink.refl` legs.  The two are not
interchangeable without changing the C5 type, so no silent type change is
made here.  The actual square is recorded and available for a future
type-level bridge. -/

theorem nativeSHEActual_nonempty :
    Nonempty (NativeSHEActual (l := l) (V := V) I) :=
  ⟨nativeSHEActual (l := l) (V := V) I⟩

end LeanFormal.IUT.N8Closure.C5DonorProof
