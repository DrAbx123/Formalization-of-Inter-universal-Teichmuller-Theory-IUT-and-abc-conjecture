import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.IPLFamilyData

noncomputable section

namespace LeanFormal.IUT.N8Closure.C5Actual

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

/-- Gate-only IPL family: the actual strip with the singleton family containing
its identity poly-isomorphism.  This is not the paper's full family and is
recorded only as a zero-sorry object; it is not used as a fake actual instance. -/
noncomputable def gateIPLFamily : IPLFamilyData I where
  source := I.fPrimeStripAt 0 0
  target := I.fPrimeStripAt 0 0
  source_eq := rfl
  target_eq := rfl
  permitted := {FPrimeStripEquiv.refl (I.fPrimeStripAt 0 0)}
  permitted_nonempty := ⟨FPrimeStripEquiv.refl (I.fPrimeStripAt 0 0), rfl⟩

/-- Exact decomposition of the C5 actual target into its four independent
components.  This is the no-go boundary: the target is inhabited iff an actual
IPL family, an actual SHE square, an actual APT instance, and the actual
permitted signed-label family are all supplied. -/
theorem sourceAlgorithmCompatibilityData_nonempty_iff :
    Nonempty (SourceAlgorithmCompatibilityData I C1 C2 C3 C4) ↔
      Nonempty (IPLFamilyData I) ∧
        Nonempty (SHERepresentation I) ∧
          Nonempty (APTRepresentation I LAdd (I.ThetaPilotPoint C4.place.v)) ∧
            ∃ P : Set (SignedLabel l.value),
              ∃ j : SignedLabel l.value, P.Nonempty ∧ j ∈ P := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨D.iplFamily⟩, ⟨D.she⟩, ⟨D.apt⟩,
      ⟨D.permitted, D.pilotLabel, D.permitted_nonempty, D.pilotLabel_mem⟩⟩
  · rintro ⟨⟨ipl⟩, ⟨she⟩, ⟨apt⟩, ⟨P, j, hP, hj⟩⟩
    exact ⟨{ iplFamily := ipl, she := she, apt := apt, permitted := P, pilotLabel := j, permitted_nonempty := hP, pilotLabel_mem := hj }⟩

end LeanFormal.IUT.N8Closure.C5Actual
