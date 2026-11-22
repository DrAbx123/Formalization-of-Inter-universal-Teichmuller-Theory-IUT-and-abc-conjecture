import tmp.sheaf.xif.paper.S583AlignedDivisorEvalS491Actual
import tmp.sheaf.xif.paper.S582AlignedDivisorEvalActual
import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S566QvPhiQOrderFieldsActual

noncomputable section
open CategoryTheory
open Iut
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

theorem positiveUnit_divisor_toLift (qOrder : ℕ) :
    (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
    grothendieckStageDivisorULift'
      (divisorMap (K := K) (L := coverField A.base) (P.valuation A.base)
        (Additive.ofMul (positiveUnit (K := K) P A qOrder))) := by
  rw [show (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
    example32DivisorAlignedS491 (K := K) (P.valuation) A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) from rfl]
  rw [example32DivisorAlignedS491_eval]

theorem positiveUnit_divisor_eval (qOrder : ℕ) :
    (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
    Algebra.GrothendieckAddGroup.of
      (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier) := by
  rw [positiveUnit_divisor_toLift (K := K) P A qOrder, divisorMap_apply]
  change grothendieckStageDivisorULift'
      (intToStageDivisorGrothendieck
        (Multiplicative.toAdd ((P.valuation A.base).valuation
          (positiveUnit (K := K) P A qOrder)))) =
    Algebra.GrothendieckAddGroup.of (ULift.up qOrder)
  rw [positiveUnit_valuation (K := K) P A qOrder,
    intToStageDivisorGrothendieck_ofNat]
  have hlift : ∀ x : StageDivisor.{u},
      (Algebra.GrothendieckAddGroup.lift
        (Algebra.GrothendieckAddGroup.of.comp stageDivisorULiftEquiv'.toAddMonoidHom))
        (Algebra.GrothendieckAddGroup.of x) =
      (Algebra.GrothendieckAddGroup.of.comp stageDivisorULiftEquiv'.toAddMonoidHom) x := by
    intro x
    have h := Algebra.GrothendieckAddGroup.lift_symm_apply
      (Algebra.GrothendieckAddGroup.lift
        (Algebra.GrothendieckAddGroup.of.comp stageDivisorULiftEquiv'.toAddMonoidHom))
    rw [Equiv.symm_apply_apply] at h
    exact congrArg (fun g => g x) h.symm
  change (Algebra.GrothendieckAddGroup.lift
      (Algebra.GrothendieckAddGroup.of.comp stageDivisorULiftEquiv'.toAddMonoidHom))
      (Algebra.GrothendieckAddGroup.of (ULift.up qOrder : StageDivisor.{u})) = _
  rw [hlift]
  rfl

end