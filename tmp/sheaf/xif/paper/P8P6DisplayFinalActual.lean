/- P8/P6 display final: G1/P8 slack plus the P6 Thm 1.10 display. -/
import tmp.sheaf.xif.paper.P8ChainSlackFinalActual
import tmp.sheaf.xif.paper.Mzk1P6DisplayFinalActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8P6DisplayFinalActual
noncomputable def p8_p6_slack_final := @LeanFormal.IUT.XiFPaper.P8ChainSlackFinalActual.p8Chain_slack
noncomputable def p8_p6_display_final := @LeanFormal.IUT.XiFPaper.Mzk1P6DisplayFinalActual.p6_display_final
#print axioms p8_p6_slack_final
#print axioms p8_p6_display_final
end LeanFormal.IUT.XiFPaper.P8P6DisplayFinalActual
end