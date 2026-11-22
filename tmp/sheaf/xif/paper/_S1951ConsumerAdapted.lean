import tmp.sheaf.xif.paper.S1951KummerEvaluationSquareActual

open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual

#check fourCorners
#check s1927Square
#check s1927Square_nonempty
#check lowerHorizontal_stripIso
#check kummerEvaluationSquare_twoPath
#check fullLogKummerUQ
#check upperEvaluation_stripIso
#check leftKummer_stripIso
#check rightKummer_stripIso

example (D : S1895PaperInput) : Nonempty (S1927KummerEvaluationSquareActual D) :=
  s1927Square_nonempty D

example (D : S1895PaperInput) :
    (kummerEvaluationSquare D).lowerHorizontal.stripIso = linkLGPToLgpLower D :=
  lowerHorizontal_stripIso D
