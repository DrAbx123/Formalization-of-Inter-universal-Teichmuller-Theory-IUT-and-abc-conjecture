import tmp.sheaf.xif.paper.S1968QVDeterminedQPilotActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual

namespace S1968Consumer

#check @paperQV
#check @paperQVOrder
#check @paperQPilotDivisor
#check @paperQPilotDivisor_deg_eq_source
#check @paperQPilotLogVolume_eq_neg_deg
#check @qvDeterminedQPilotObject
#check @R6Proper
#check @r6Proper_iff
#check @r6Proper_forces_trivial_timesMu
#check @availableStrip_not_qvDetermined
#check @s1968_status

example (D : S1895PaperInput) : Nonempty (QVDeterminedQPilotObject D) :=
  qvDeterminedQPilotObject_exists D

example (D : S1895PaperInput) (P : SourceFTimesMuPrimeStrip PaperV) :
    R6Proper D P ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence (reducedQPilotTimesMu D) P) :=
  s1968_r6_exact_reduction D P

example (D : S1895PaperInput) (v : PaperV) :
    Subsingleton ((reducedQPilotTimesMu D).timesMu v) :=
  reducedQPilotTimesMu_subsingleton D v

#print axioms s1968_status

end S1968Consumer
