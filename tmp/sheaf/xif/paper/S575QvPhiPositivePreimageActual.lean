import tmp.sheaf.xif.paper.S566QvPhiQOrderFieldsActual
import tmp.sheaf.xif.paper.S412DvTriangleTauActual
import tmp.sheaf.xif.paper.S456RationalInclusionActual
import tmp.sheaf.xif.paper.S491AlignedDivisorMapActual
import tmp.sheaf.xif.paper.S465LiftedDivisorMapActual
import tmp.sheaf.xif.paper.S457DivisorMapActual
import tmp.sheaf.xif.paper.S481AlignedDivisorMapActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual
import tmp.sheaf.xif.paper.S583AlignedDivisorEvalS491Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S583AlignedDivisorEvalS491Actual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid
open Additive

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

/-- Actual unit with qOrder valuation exponent. -/
noncomputable def positiveUnit (qOrder : ℕ) : (coverField A.base)ˣ :=
  Classical.choose ((P.valuation A.base).valuation_surjective (qOrder : ℤ))

theorem positiveUnit_valuation (qOrder : ℕ) :
    Multiplicative.toAdd ((P.valuation A.base).valuation
      (positiveUnit (K := K) P A qOrder)) = (qOrder : ℤ) :=
  Classical.choose_spec ((P.valuation A.base).valuation_surjective (qOrder : ℤ))

/-- S585 formula: aligned divisor of the positive unit is the qOrder generator. -/
theorem positiveUnit_divisor (qOrder : ℕ) :
    (s566Input (K := K) P).divisor A.base
        (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
      Algebra.GrothendieckAddGroup.of
        (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier) := by
  rw [show (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder)))
      = example32DivisorAlignedS491 (K := K) (P.valuation) A.base
          (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) from rfl]
  rw [example32DivisorAlignedS491_eval (K := K) (V := P.valuation) (X := A.base)
    (u := positiveUnit (K := K) P A qOrder)]
  rw [divisorMap_apply]
  change grothendieckStageDivisorULift'
      (intToStageDivisorGrothendieck
        (Multiplicative.toAdd ((P.valuation A.base).valuation
          (positiveUnit (K := K) P A qOrder)))) =
    Algebra.GrothendieckAddGroup.of (ULift.up qOrder)
  rw [positiveUnit_valuation (K := K) P A qOrder, intToStageDivisorGrothendieck_ofNat]
  rw [grothendieckStageDivisorULift'_of]
  simp [stageDivisorULiftEquiv']
  congr 1

/-- Exact positive qOrder preimage. -/
structure PositiveQvPhiPreimage (qOrder : ℕ) where
  qOrder_pos : 0 < qOrder
  rationalFunction : (s566Input (K := K) P).rationalFunctions.obj A.base
  divisor : ((qvPhi (K := K) P.ramification).obj A.base).carrier
  divisor_eq : (s566Input (K := K) P).divisor A.base rationalFunction =
    Algebra.GrothendieckAddGroup.of divisor

def PositiveQvPhiPreimageRequired (qOrder : ℕ) : Prop :=
  Nonempty (PositiveQvPhiPreimage (K := K) P A qOrder)

/-- Explicit positive preimage using positiveUnit. -/
noncomputable def positiveQvPhiPreimage
    (qOrder : ℕ) (hq : 0 < qOrder) :
    PositiveQvPhiPreimage (K := K) P A qOrder where
  qOrder_pos := hq
  rationalFunction := Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))
  divisor := (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier)
  divisor_eq := positiveUnit_divisor (K := K) P A qOrder

end LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual

end