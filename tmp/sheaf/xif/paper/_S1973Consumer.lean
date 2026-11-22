import tmp.sheaf.xif.paper.S1973PsiCnsActual

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1966LocalThetaMonoidActual
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual

namespace LeanFormal.IUT.XiFPaper.S1973PsiCnsConsumer

#check PsiCnsModel
#check psiCnsAction
#check psiCns_smul_mul
#check psiCnsEquivSourceMLF
#check psiCnsUnitsEquivSourceMLF_smul
#check PsiCnsJointContinuousActionMissing
#check diagonalFlStarUnits
#check diagonalFlStarUnits_card
#check diagonalFlStarUnits_galois_smul_mem
#check diagonalFlStarUnitsInGau_val_mem_localGaussian
#check PsiEnvModel
#check PsiGauModel
#check psiEvaluation
#check psiEvaluation_bijective
#check psiEvaluation_units
#check psiEvaluation_generator
#check psiEvaluation_unitSection
#check psiEvaluation_raySection

example (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Nat.card (diagonalFlStarUnits v l) = l.value - 1 :=
  diagonalFlStarUnits_card v l

example (v : FinitePrimePlace 2 7) (l : PrimeGeFive) :
    Function.Bijective (psiEvaluation v l) :=
  psiEvaluation_bijective v l

#print axioms diagonalFlStarUnits_card
#print axioms psiEvaluation_unitSection
#print axioms psiEvaluation_raySection

end LeanFormal.IUT.XiFPaper.S1973PsiCnsConsumer
