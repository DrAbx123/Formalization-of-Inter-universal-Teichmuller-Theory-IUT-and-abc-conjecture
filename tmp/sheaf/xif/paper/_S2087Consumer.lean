import tmp.sheaf.xif.paper.S2087AffineQuotientPackagingActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2087AffineQuotientPackagingActual

#check @affineQuotientColimitPackaging
#check @s2073AffineActionCoconeIsColimit
#check @affineHasColimitsOfShape
#check @curveHasQuotients
#check @curveS2073HasQuotients
#check @curvePreGaloisRemainingFields

example (K : Type) [Field K] :
    LeanFormal.IUT.IUTII.Frobenioid.Example36.CurvePreGaloisCategoryRemainingFields
      (LeanFormal.IUT.IUTII.Frobenioid.Example36.curveScheme K) :=
  curvePreGaloisRemainingFields K

example (K : Type) [Field K] :
    LeanFormal.IUT.XiFPaper.S2072HasQuotientsActual.AffineQuotientColimitPackaging
      (LeanFormal.IUT.IUTII.Frobenioid.Example36.curveCoordinateRing K) :=
  curveAffineQuotientColimitPackaging K

#print axioms curvePreGaloisRemainingFields

end
