import tmp.sheaf.xif.paper.S507PhiCvCandidateActual
import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual
import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S614PhiCvModelComparisonActual
open CategoryTheory
open Iut
open Iut.SourceFinitePlaceReconstruction
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S507PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K] [NumberField K]

structure PhiCvModelComparison (place : NumberField.FinitePlace K)
    (R : S511PhiCvCandidateActual.RamificationIndexData (K := K)) where
  baseEquiv : StageBase place ≃ Example32SmallBase K
  carrierEquiv : ∀ X : StageBase place,
    StageDivisor.{u} ≃+
      ((qvPhi (K := K) R).obj (baseEquiv X)).carrier
  divisor_compat : Prop
  phi_compat : Prop

noncomputable def phiCvModelComparisonOf
    (place : NumberField.FinitePlace K)
    (R : S511PhiCvCandidateActual.RamificationIndexData (K := K))
    (baseEquiv : StageBase place ≃ Example32SmallBase K)
    (carrierEquiv : ∀ X : StageBase place,
      StageDivisor.{u} ≃+
        ((qvPhi (K := K) R).obj (baseEquiv X)).carrier)
    (divisor_compat phi_compat : Prop)
    (hdiv : divisor_compat) (hphi : phi_compat) :
    PhiCvModelComparison place R where
  baseEquiv := baseEquiv
  carrierEquiv := carrierEquiv
  divisor_compat := divisor_compat
  phi_compat := phi_compat

def PhiCvModelComparisonRequired (place : NumberField.FinitePlace K)
    (R : S511PhiCvCandidateActual.RamificationIndexData (K := K)) : Prop :=
  Nonempty (PhiCvModelComparison place R)

end LeanFormal.IUT.XiFPaper.S614PhiCvModelComparisonActual
end