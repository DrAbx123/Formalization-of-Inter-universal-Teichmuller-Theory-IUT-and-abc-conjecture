import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual

/-! # S1013: re-audit of S995

S1005 is still absent from D:\lean (global search).  This file audits the
current S995: s995Cor312Conclusion has target exactly Cor312Conclusion; its
axioms and those of the underlying finite-carrier theorem are printed. -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual

#check s995Cor312Conclusion
#print axioms s995Cor312Conclusion
#print axioms s995FiniteCarrierCor312Conclusion

end
