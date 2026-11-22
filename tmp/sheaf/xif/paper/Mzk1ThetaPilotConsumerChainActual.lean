import tmp.sheaf.xif.paper.Mzk1ThetaPilotPacketInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ThetaPilotKummerLinkActual
import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual

/-!
# Mzk1ThetaPilotConsumerChainActual — consumer theorems for theta-pilot assets
(TPI/TKL/IKT, all EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotKummerLinkActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual

/-- Consumer: theta-pilot tensor generator lies in the IQ packet (TPI). -/
theorem consumer_thetaPilot_generator (D : SourceLogShellDatum) (j : ℕ)
    (f : (i : Capsule j) → D.K) (hf : ∀ i, f i ∈ D.logShell) :
    sourceLogShellTensorGenerator D j f ∈ sourceThetaPilotIQPacket D j :=
  tensorGenerator_mem_iqPacket D j f hf

/-- Consumer: the theta-pilot/Kummer link interface is nonempty (TKL). -/
theorem consumer_link_nonempty (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type) [Group G] : Nonempty (ThetaPilotKummerLink K n hμ G) :=
  thetaPilotKummerLink_nonempty K n hμ G

/-- Consumer: the link's packet rows have the expected length (TPI). -/
theorem consumer_packet_rows_length : thetaPilotPacketRows.length = 7 :=
  thetaPilotPacketRows_length

#check consumer_thetaPilot_generator
#check consumer_link_nonempty
#check consumer_packet_rows_length

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotConsumerChainActual
end
