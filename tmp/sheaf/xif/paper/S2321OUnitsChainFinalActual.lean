import tmp.sheaf.xif.paper.S2286StripChainActual
import tmp.sheaf.xif.paper.S2302TorsionRetractionActual

/-! # S2321: final conditional paper O^×μ chain

Under S2135 prime alignment, the strip identification, quotient automorphism,
unit log-Kummer lift, S2222 attachment, and S2245 log-Kummer datum are all
actual.  The final structure records the whole chain; nonemptiness is equivalent
to S2135, with no part of the chain fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2321OUnitsChainFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual
open LeanFormal.IUT.XiFPaper.S2245LogKummerActual
open LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
open LeanFormal.IUT.XiFPaper.S2286StripChainActual
open LeanFormal.IUT.XiFPaper.S2288UnitLiftActual
open LeanFormal.IUT.XiFPaper.S2302TorsionRetractionActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The full paper O^×μ chain, conditional on S2135. -/
structure S2321OUnitsChain
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  stripIdentification : S2249StripQuotientIdentificationRequired T b
  muAut : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b
  unitLift : S2249LogKummerOnUnitsRequired T b
  attachment : S2222PaperOUnitsMuAttachment T b
  logKummer : S2245LogKummerRequired T b

noncomputable def s2321OUnitsChainOfPrimeAlignment
    (h : S2135PrimeAlignmentRequired T b) :
    S2321OUnitsChain T b where
  primeAlignment := h
  stripIdentification := s2286StripQuotientIdentification T b h
  muAut := s2286MuAut T b h
  unitLift := s2302LogKummerOnUnitsOfStrip T b h
  attachment := s2222Attachment T b
  logKummer := s2249ToS2245 T b (s2302LogKummerOnUnitsOfStrip T b h)

theorem s2321Chain_iff_primeAlignment :
    Nonempty (S2321OUnitsChain T b) ↔ S2135PrimeAlignmentRequired T b :=
  ⟨fun ⟨C⟩ => C.primeAlignment,
    fun h => ⟨s2321OUnitsChainOfPrimeAlignment T b h⟩⟩

def S2321RemainingRequired : Prop :=
  S2135PrimeAlignmentRequired T b

theorem s2321Remaining_iff_chain :
    S2321RemainingRequired T b ↔ Nonempty (S2321OUnitsChain T b) :=
  (s2321Chain_iff_primeAlignment T b).symm

#check S2321OUnitsChain
#check s2321OUnitsChainOfPrimeAlignment
#check s2321Chain_iff_primeAlignment
#check S2321RemainingRequired
#check s2321Remaining_iff_chain

end LeanFormal.IUT.XiFPaper.S2321OUnitsChainFinalActual
end
