import Mathlib.Algebra.Group.TypeTags.Basic
import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S583AlignedDivisorEvalS491Actual
import tmp.sheaf.xif.paper.S565QvOrderFromS556InputActual
import tmp.sheaf.xif.paper.S566QvPhiQOrderFieldsActual

/-! # S584: S556QOrderWitness from positiveUnit + aligned divisor eval -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S584QOrderWitnessActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S565QvOrderFromS556InputActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S583AlignedDivisorEvalS491Actual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid
open Additive

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

theorem positiveUnit_divisor_evalS584 (qOrder : ℕ) :
    (s566Input P).divisor A.base
        (Additive.ofMul (ULift.up (positiveUnit P A qOrder))) =
      Algebra.GrothendieckAddGroup.of
        (ULift.up qOrder : ((qvPhi P.ramification).obj A.base).carrier) := by
  change (grothendieckStageDivisorULift'.comp
      (liftedDivisorMap (K := K) (L := coverField A.base) (P.valuation A.base)))
      (Additive.ofMul (ULift.up (positiveUnit P A qOrder))) = _
  rw [AddMonoidHom.comp_apply, liftedDivisorMap_apply, divisorMap_apply]
  simp only [toMul_ofMul, ofMul_toMul]
  rw [positiveUnit_valuation]
  rw [intToStageDivisorGrothendieck_ofNat]
  rw [grothendieckStageDivisorULift'_of, stageDivisorULiftEquiv'_ulift_up]

noncomputable def s556QOrderWitnessActual :
    S556QOrderWitness (K := K) T b (s561InputData (K := K) P) A where
  rationalFunction := Additive.ofMul
    (ULift.up (positiveUnit P A (qVFamilyK T b).order))
  divisor_eq := positiveUnit_divisor_evalS584 (P := P) (A := A)
    (qOrder := (qVFamilyK T b).order)

end LeanFormal.IUT.XiFPaper.S584QOrderWitnessActual
end
