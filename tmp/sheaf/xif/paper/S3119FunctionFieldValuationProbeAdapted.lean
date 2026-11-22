import tmp.sheaf.xif.paper.S3119InfinityValuationActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119InfinityValuationActual
namespace LeanFormal.IUT.XiFPaper.S3119FunctionFieldValuationProbeAdapted
set_option backward.isDefEq.respectTransparency false
variable {l : PrimeGeFive}
noncomputable def test : AddValuation (WeierstrassCurve.Affine.FunctionField (W l)) (WithTop ℤ) :=
  AddValuation.ofValuation
    (Valuation.extendToLocalization
      (AddValuation.toValuation (S3119InfinityAddValuation l))
      (by
        intro s hs
        -- TODO
        exact ?_)
      (WeierstrassCurve.Affine.FunctionField (W l)))
#check test
end LeanFormal.IUT.XiFPaper.S3119FunctionFieldValuationProbeAdapted
end
