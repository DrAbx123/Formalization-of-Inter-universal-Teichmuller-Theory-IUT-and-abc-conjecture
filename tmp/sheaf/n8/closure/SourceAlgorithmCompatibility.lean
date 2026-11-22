import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.IPLFamilyData
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportLaws
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceAdjacentColumnProcessionIsomorphism

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility

universe ua uv upi umon ui uL uOut uG uV uMid

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

abbrev Output : Type _ := I.ThetaPilotPoint C4.place.v

/-- IPL representation on a shared Label/Choice carrier. -/
structure IPLRepresentation (LAdd : Type uG) (Choice : Type uOut) [AddGroup LAdd] where
  core1 : Core LAdd Choice
  core2 : Core LAdd Choice
  link : LinkSpan.{uG, uOut, uOut} core1 core2
  supply : CardIPLTransportSupply.{uG, uOut, uOut, uOut} link
  kummerEval : KummerEvaluationFactor.{uG, uOut, uOut} link
  kummerEval_eq : kummerEval = supply.kummerEval

/-- SHE representation: the actual four-leg simultaneity square. -/
structure SHERepresentation (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  square : SourceSimultaneousHolomorphicExpression
    (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 0)
    (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 0)
    (FPrimeStripLink.refl (I.fPrimeStripAt 0 0)) (FPrimeStripLink.refl (I.fPrimeStripAt 0 0))
    (FPrimeStripLink.refl (I.fPrimeStripAt 0 0)) (FPrimeStripLink.refl (I.fPrimeStripAt 0 0))

/-- APT representation: actual parallel transport and adjacent-column
procession isomorphism for the same source algorithm. -/
structure APTRepresentation (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (LAdd : Type uG) [AddGroup LAdd] (Y : Type uOut) where
  S : SourceOneColumnArithmeticHolomorphicStructure V
  A : SourceTheorem311MultiradialAlgorithm (Multiplicative LAdd)
    (Multiplicative LAdd) I 0 Y
  transport : SourceAlgorithmicParallelTransport S A A
  procession : SourceProcessionIsomorphism I 0 0

/-- The three representations of the same actual source algorithm, plus
the operation correspondence linking them to the C4 algorithm actions. -/
structure SourceAlgorithmCompatibilityData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  iplFamily : IPLFamilyData I
  she : SHERepresentation I
  apt : APTRepresentation I LAdd (I.ThetaPilotPoint C4.place.v)
  /-- The permitted family of source signed labels. -/
  permitted : Set (SignedLabel l.value)
  /-- The actual source pilot label selected from the permitted family. -/
  pilotLabel : SignedLabel l.value
  /-- The permitted family is nonempty. -/
  permitted_nonempty : permitted.Nonempty
  /-- The pilot label belongs to the permitted family. -/
  pilotLabel_mem : pilotLabel ∈ permitted

/-- C5 stage-2 existence obligation.  The three representations are actual
donor records over the same C4 output; operation correspondence is recorded
as equalities with the actual algorithm actions.  The construction of an
actual instance (C2/C3/C4/C5 data, common C4/algorithm bridge, Remark 3.10.2
composite) is the named gap. -/
theorem sourceAlgorithmCompatibility_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) :
    Nonempty (SourceAlgorithmCompatibilityData I C1 C2 C3 C4) := by
  sorry

end LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
