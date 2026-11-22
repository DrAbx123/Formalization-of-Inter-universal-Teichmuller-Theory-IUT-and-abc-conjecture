/-
Probe for S2441: check the API needed for the range cycle-type reduction.
-/
import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual

noncomputable section

open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual

#check @S2243GLMap_eq_id
#check @S2243TransferredRange_eq
#check @S2218PairPerm
#check @S2218PairPerm_apply
#check @S2132cycleType_permCongr
#check @S2056PairMap
#check @S2056NonzeroTorsionMap
#check @S2056PointMap
#check @S1906ProjAffineEquiv
#check @S2172AffineBasis
#check @S2172AffineTorsionEquiv
#check @PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation_acts
#check @PuncturedEllipticCurve.galoisActionOnPoint
#check @S2218PairEquiv
#check @S2180PairMap
#check @S2186BasisCompatiblePairEquiv
#check @WeierstrassCurve.Affine.Point.map_map
#check @Matrix.GeneralLinearGroup.toLin
#check @Matrix.GeneralLinearGroup.toLin_apply
#check @Matrix.GeneralLinearGroup.toLin_toLinearEquiv
#check @Matrix.GeneralLinearGroup.toLin'_apply
#check @S2229GaloisPairPerm
#check @S2229GaloisGroup
#check @S2056PairMap
#check @S2056Ne_neg
#check @S2056NonzeroTorsionMap_neg

end
