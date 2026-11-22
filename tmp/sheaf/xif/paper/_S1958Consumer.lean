import tmp.sheaf.xif.paper.S1958FullLogKummerUQActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual

#check @paperFullLogKummerUQ
#check @s1927FullLogKummerUQ_inhabited
#check @paperFullLogKummerUQ_attached_to_paperO
#check @paperFullLogKummerUQ_logShell_eq_closedBall

-- The exact target, as stated for S1958.
example (D : S1895PaperInput) : Nonempty (S1927FullLogKummerUQ D) :=
  s1927FullLogKummerUQ_inhabited D

-- The package's (1,0) data are the paper O object's data.
example (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).oneColumn = (S1895PaperO D).oneColumn :=
  paperFullLogKummerUQ_oneColumn D

-- The square component is inhabited at the actual source strips.
example (D : S1895PaperInput) :
    Nonempty (S1927KummerEvaluationSquareActual D) :=
  (s1927FullLogKummerUQ_nonempty_iff_kummerSquare D).mp
    (s1927FullLogKummerUQ_inhabited D)

#print axioms LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual.s1927FullLogKummerUQ_inhabited
#print axioms LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual.paperFullLogKummerUQ_attached_to_paperO

end
