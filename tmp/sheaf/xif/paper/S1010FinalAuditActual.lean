import tmp.sheaf.xif.paper.S1000FinalCor312AssemblyActual

/-! # S1010: audit of the S1000 final assembly

S1005 is not present in the tree.  This audit checks the existing final
assembly S1000: its target is Cor312Conclusion (as a conjunct), the proof uses
only the declared S994/S995 inputs, and no sorry/axiom/True/PUnit occurs in the
S1000/S995/S994/S983/S991 chain. -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S1000FinalCor312AssemblyActual

#check s1000FinalCor312
#print axioms s1000FinalCor312

end
