import tmp.sheaf.xif.paper.S1959PaperCoricVerticesActual

open LeanFormal.IUT.XiFPaper.S1959PaperCoricVerticesActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual

#check reducedSquare
#check reducedSquare_commutes
#check fourSourceStrips_from_distinct_theaters
#check ReducedVertex.upperEvaluation_strip
#check leftKummer_layer_equiv

example (D : S1895PaperInput) :
    Nonempty (LeanFormal.IUT.SourceFTimesMuPrimeStripPolyIsomorphismSquare
      (ReducedVertex.env D) (ReducedVertex.gau D)
      (ReducedVertex.LGP D) (ReducedVertex.lgp D)) :=
  ⟨reducedSquare D⟩

#print axioms reducedSquare
#print axioms fourSourceStrips_from_distinct_theaters