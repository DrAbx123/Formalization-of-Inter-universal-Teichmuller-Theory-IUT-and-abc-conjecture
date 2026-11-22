import tmp.sheaf.xif.paper.S607ModelPaperPhiAlignmentActual
import tmp.sheaf.xif.paper.S547PhiCvPackageActual

/-! # S616: partial ModelPaperPhiAlignment

The base self-equivalence of the S522 model is actual (`Equivalence.refl`).
No independent paper `Phi_Cv^+` carrier with the S607 paper predicate `True`
is present in S547/S522: S547's package phi is the S522 model with IsFSM=IsIso,
and its N*qOrder submonoid lives on `ULift ℕ`, not on a separate paper carrier.
Therefore `phiObjEquiv` to an actual paper carrier is recorded exactly; no
tautological self-alignment is presented as paper alignment.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S616ModelPaperAlignmentActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S607ModelPaperPhiAlignmentActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))

/-- Actual base self-equivalence of the S522 model. -/
def s616ModelBaseEquiv : Example32SmallBase K ≌ Example32SmallBase K :=
  CategoryTheory.Equivalence.refl

/-- Exact missing paper carrier and phiObjEquiv to the S522 model. -/
structure S616PaperPhiObjEquivData where
  paperBase : Type (u+1)
  [paperCategory : Category paperBase]
  paperPhi : DivisorialMonoidOn.{u+1} paperBase (fun {_ _} _ => True)
  baseEquiv : Example32SmallBase K ≌ paperBase
  phiObjEquiv : Prop
  phiPullback_comm : Prop
  split_eq : Prop

def S616PaperPhiObjEquivDataRequired : Prop :=
  Nonempty (S616PaperPhiObjEquivData K R)

end LeanFormal.IUT.XiFPaper.S616ModelPaperAlignmentActual
end
