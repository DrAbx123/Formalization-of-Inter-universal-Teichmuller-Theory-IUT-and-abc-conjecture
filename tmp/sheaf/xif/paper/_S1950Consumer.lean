import tmp.sheaf.xif.paper.S1950ArchimedeanLogShellActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual

#check @LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual.paperArchimedeanLogShell
#check @LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual.paperArchimedeanLogShellDatum
#check @LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual.paperFullLogKummerUQ_nonempty_iff_kummerSquare_nonempty
#print axioms LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual.paperArchimedeanLogShell

example (D : S1895PaperInput) : Nonempty (S1927FirstMissing D) :=
  LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual.s1950FirstMissing_inhabited D

example (D : S1895PaperInput) :
    Nonempty (S1927FullLogKummerUQ D) ↔
      Nonempty (S1927KummerEvaluationSquareActual D) :=
  LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual.paperFullLogKummerUQ_nonempty_iff_kummerSquare_nonempty D

end
