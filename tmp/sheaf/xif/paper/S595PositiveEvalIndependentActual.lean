import tmp.sheaf.xif.paper.S583AlignedDivisorEvalS491Actual
import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S595PositiveEvalIndependentActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S583AlignedDivisorEvalS491Actual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid
open Additive

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

theorem positiveUnit_divisor_eval
    (qOrder : ℕ) :
    (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
    Algebra.GrothendieckAddGroup.of
      (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier) := by
  rw [show (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder)))
      = example32DivisorAlignedS491 (K := K) (P.valuation) A.base
          (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) from rfl]
  rw [example32DivisorAlignedS491_eval (K := K) (V := P.valuation)
    (X := A.base) (u := positiveUnit (K := K) P A qOrder)]
  rw [divisorMap_apply]
  change grothendieckStageDivisorULift'
      (intToStageDivisorGrothendieck
        (Multiplicative.toAdd ((P.valuation A.base).valuation
          (positiveUnit (K := K) P A qOrder)))) =
    Algebra.GrothendieckAddGroup.of (ULift.up qOrder)
  rw [positiveUnit_valuation (K := K) P A qOrder,
    intToStageDivisorGrothendieck_ofNat]
  rw [S583AlignedDivisorEvalS491Actual.grothendieckStageDivisorULift'_of]
  rw [S583AlignedDivisorEvalS491Actual.stageDivisorULiftEquiv'_ulift_up]

noncomputable def positivePreimage
    (qOrder : ℕ) (hpos : 0 < qOrder) :
    PositiveQvPhiPreimage (K := K) P A qOrder where
  qOrder_pos := hpos
  rationalFunction :=
    Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))
  divisor := (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier)
  divisor_eq := positiveUnit_divisor_eval (K := K) P A qOrder

end LeanFormal.IUT.XiFPaper.S595PositiveEvalIndependentActual

end
