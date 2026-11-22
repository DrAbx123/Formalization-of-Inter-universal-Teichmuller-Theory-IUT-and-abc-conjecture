import tmp.sheaf.xif.paper.S591PositiveUnitDivisorEvalActual
import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S596PositivePreimageActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid
open Additive

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

noncomputable def positivePreimage (qOrder : ℕ) (hpos : 0 < qOrder) :
    PositiveQvPhiPreimage (K := K) P A qOrder where
  qOrder_pos := hpos
  rationalFunction := Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))
  divisor := (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier)
  divisor_eq := positiveUnit_divisor_eval (K := K) P A qOrder

end LeanFormal.IUT.XiFPaper.S596PositivePreimageActual

end
