import tmp.sheaf.xif.paper.S3128RelPullbackConeActual

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3128RelPullbackConeActual

namespace LeanFormal.IUT.XiFPaper.S3128HasPullbacksActual

variable {l : PrimeGeFive}

/-- Witness: the chosen representable cover category has pullbacks. -/
theorem S3128HasPullbacks_witness :
    HasPullbacks (S3127Cover (l := l)) :=
  S3128HasPullbacks (l := l)

#check S3128HasPullbacks_witness
#print axioms S3128HasPullbacks_witness

end LeanFormal.IUT.XiFPaper.S3128HasPullbacksActual
end