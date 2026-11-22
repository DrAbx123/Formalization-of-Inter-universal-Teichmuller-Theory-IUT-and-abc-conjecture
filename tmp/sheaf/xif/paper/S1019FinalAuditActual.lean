import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
import tmp.sheaf.xif.paper.S1007QPilotPositivityActual
import tmp.sheaf.xif.paper.S1008S1004HullFiniteActual

/-! # S1019: final audit of S995 + S1007 + S1008

S1006 does not exist as a file.  S1007 supplies positivity of the finite
qPilot image from openness of F(cRoot); S1008 supplies finiteness of the finite
hull.  S995 supplies the exact Cor312Conclusion.  This file prints targets and
axioms for all three. -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S1007QPilotPositivityActual
open LeanFormal.IUT.XiFPaper.S1008S1004HullFiniteActual

#check s995Cor312Conclusion
#print axioms s995Cor312Conclusion

#check s1007QPilotImage_measure_pos_of_open
#print axioms s1007QPilotImage_measure_pos_of_open

#check s1008Hull_measure_lt_top
#print axioms s1008Hull_measure_lt_top

end
