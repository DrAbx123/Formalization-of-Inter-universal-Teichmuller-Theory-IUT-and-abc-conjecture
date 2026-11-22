import tmp.sheaf.xif.paper.S1812InverseModelHomActual

/-- The compiled olean can be imported and its statements used. -/
example (A B : LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728Cover)
    (h : LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual.S1755SourceRetraction)
    (g : LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual.S1812ModelHomOver A B) :
    LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual.S1755ModelHomOfCoverMap A B
        (LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual.S1812ModelHomToCoverMap A B g) = g.1 :=
  LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual.S1812ModelHomOfCoverMap_toCoverMap h A B g

#check LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual.S1812ModelHomEquivMissing_iff
