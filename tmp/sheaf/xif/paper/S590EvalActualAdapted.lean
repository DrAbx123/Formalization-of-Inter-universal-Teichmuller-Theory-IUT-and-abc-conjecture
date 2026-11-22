import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S491AlignedDivisorMapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S590EvalActualAdapted

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
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

example (qOrder : ℕ) :
    (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
    Algebra.GrothendieckAddGroup.of
      (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier) := by
  simp only [s566Input, s561Input, s556InputActual]
  change grothendieckStageDivisorULift'
      (divisorMap (P.valuation A.base)
        (Additive.ofMul (positiveUnit (K := K) P A qOrder))) =
    Algebra.GrothendieckAddGroup.of (ULift.up qOrder)
  rw [divisorMap_apply]
  simp only [Additive.toMul_ofMul]
  have hpow : Multiplicative.toAdd
      ((P.valuation A.base).valuation (positiveUnit (K := K) P A qOrder)) = (qOrder : ℤ) :=
    positiveUnit_valuation (K := K) P A qOrder
  rw [hpow, intToStageDivisorGrothendieck_ofNat]
  rfl

end LeanFormal.IUT.XiFPaper.S590EvalActualAdapted
end