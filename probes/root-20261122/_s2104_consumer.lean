import tmp.sheaf.xif.paper.S2104TorsionCompletionActual

noncomputable section

open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2104TorsionCompletionActual

variable {p : Nat} [Fact (Nat.Prime p)] (U : Index p)

example : CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U :=
  torsionCompletionEquivMu U

example : Nonempty (CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U) :=
  ⟨torsionCompletionEquivMu U⟩

#check torsionCompletionEquivMu
#check torsionCompletionIso_holds
#print axioms torsionCompletionEquivMu
#print axioms torsionCompletionIso_holds

end
