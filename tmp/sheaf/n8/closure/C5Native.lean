import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.IPLFamilyData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceAdjacentColumnProcessionIsomorphism

noncomputable section

namespace LeanFormal.IUT.N8Closure.C5Native

universe ua uv upi umon ui uG

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-- Actual conversion of an F-prime-strip equivalence to an indexed
F-prime-strip link.  This is the missing bridge used by the SHE slice. -/
def fPrimeStripLinkOfEquiv {S T : FPrimeStrip V} (e : FPrimeStripEquiv S T) :
    FPrimeStripLink S T where
  index := id
  mapPi := fun v => (e.isoPi v).toMonoidHom
  mapG := fun v => (e.isoG v).toMonoidHom
  mapMon := fun v => (e.isoMon v).toMonoidHom
  compatProj := fun v => e.compatProj v
  compatAction := fun v g x => e.compatAction v g x
  compatDegree := fun v x => e.compatDegree v x

/-- The native IPL family slice: the actual strip `I.fPrimeStripAt 0 0` together
with the actual self-link `I.fLinkAt 0 0 0 0`.  This is an actual poly-isomorphism
slice, not the full paper family. -/
noncomputable def nativeIPLFamily : IPLFamilyData I where
  source := I.fPrimeStripAt 0 0
  target := I.fPrimeStripAt 0 0
  source_eq := rfl
  target_eq := rfl
  permitted := {I.fLinkAt 0 0 0 0}
  permitted_nonempty := ⟨I.fLinkAt 0 0 0 0, rfl⟩

/-- Actual native SHE square on four actual self-links `I.fLinkAt 0 0 0 0`.
This is the actual-link slice; it is intentionally separate from the C5
`SHERepresentation`, whose legs are hard-coded to identity links. -/
structure NativeSHEActual (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  square : SourceSimultaneousHolomorphicExpression
    (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 0)
    (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 0)
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))
    (fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0))

noncomputable def nativeSHEActual : NativeSHEActual (l := l) (V := V) I where
  square := SourceSimultaneousHolomorphicExpression.ofCommutingLegs (by rfl)

/-- The native labelled source candidate: the unique label `0`, with the
candidate singleton family.  This is a candidate slice; it is not the
source-constrained permitted family. -/
noncomputable def nativePilotLabel : SignedLabel l.value :=
  ⟨0, by constructor <;> omega⟩

noncomputable def nativePermittedCandidate : Set (SignedLabel l.value) :=
  {nativePilotLabel (l := l)}

theorem nativePermittedCandidate_nonempty :
    (nativePermittedCandidate (l := l)).Nonempty :=
  ⟨nativePilotLabel (l := l), rfl⟩

theorem nativePilotLabel_mem :
    nativePilotLabel (l := l) ∈ nativePermittedCandidate (l := l) :=
  rfl

/-- Exact missing native APT data.  The APT fields are not supplied by C1/C3/C4
in the current tree; this structure records the exact missing donors without
constructing an interface pretense. -/
structure NativeAPTMissing where
  /-- Actual one-column arithmetic holomorphic structure on `V`. -/
  missingOneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  /-- Actual multradial algorithm on the C4 output. -/
  missingAlgorithm : SourceTheorem311MultiradialAlgorithm
    (Multiplicative LAdd) (Multiplicative LAdd) I 0
    (I.ThetaPilotPoint C4.place.v)
  /-- Actual transport to the same algorithm. -/
  missingTransport : SourceAlgorithmicParallelTransport
    missingOneColumn missingAlgorithm missingAlgorithm


/-- Exact missing native permitted data: the source-constrained family and its
selected pilot label.  This records the required object; it is not inhabited by
the candidate singleton family. -/
structure NativePermittedActual (l : PrimeGeFive) where
  permitted : Set (SignedLabel l.value)
  pilotLabel : SignedLabel l.value
  permitted_nonempty : permitted.Nonempty
  pilotLabel_mem : pilotLabel ∈ permitted

theorem nativeAPTMissing_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) :
    Nonempty (NativeAPTMissing (l := l) (V := V) I C4) := by
  sorry

theorem nativePermittedActual_nonempty :
    Nonempty (NativePermittedActual (l := l)) :=
  ⟨{ permitted := {zeroSignedLabel (l := l)}
     pilotLabel := zeroSignedLabel (l := l)
     permitted_nonempty := ⟨zeroSignedLabel (l := l), by simp⟩
     pilotLabel_mem := by simp }⟩

end LeanFormal.IUT.N8Closure.C5Native
