import tmp.sheaf.xif.paper.S556QvPhiInputActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S562QvPhiInputPackageActual
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open Iut.SourceModelFrobenioid
universe u
structure QvPhiInputPackage (K : Type u) [Field K]
    (D : S556InputDataActual (K := K)) where
  R : S511PhiCvCandidateActual.RamificationIndexData (K := K)
  V : @DvSmallValuationFamily K _
  input : Input (qvPhiRamificationModel (K := K) R)
  rationalFunctions_eq :
    (s556InputActual (K := K) D).rationalFunctions =
      example32RationalFunctionsIso (K := K)
  divisor_eq :
    (s556InputActual (K := K) D).divisor =
      (fun X => example32DivisorAlignedS491 (K := K) V X)
noncomputable def qvPhiInputPackage (K : Type u) [Field K]
    (D : S556InputDataActual (K := K)) : QvPhiInputPackage K D where
  R := D.ramification
  V := D.valuationFamily
  input := s556InputActual (K := K) D
  rationalFunctions_eq := rfl
  divisor_eq := rfl
end LeanFormal.IUT.XiFPaper.S562QvPhiInputPackageActual
end