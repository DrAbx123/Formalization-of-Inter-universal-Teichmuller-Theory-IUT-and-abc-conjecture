import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-!
# Mzk1InitialThetaConsumerActual — consumer theorems over the initial theta data/signatures
(tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaConsumerActual

open LeanFormal.IUT

/-- Consumer: the (1,1)-signature has genus 1. -/
theorem consumer_typeOneOne_genus : typeOneOne.genus = 1 :=
  typeOneOne_genus

/-- Consumer: the (1,1)-signature has one puncture. -/
theorem consumer_typeOneOne_punctures : typeOneOne.punctures = 1 :=
  typeOneOne_punctures

/-- Consumer: the (1,1)-signature has no stacky orders. -/
theorem consumer_typeOneOne_stackyOrders : typeOneOne.stackyOrders = [] :=
  typeOneOne_stackyOrders

/-- Consumer: the (1,l-torsion)-signature has genus 1. -/
theorem consumer_typeOneLTorsion_genus (l : PrimeGeFive) :
    (typeOneLTorsion l).genus = 1 :=
  typeOneLTorsion_genus l

/-- Consumer: the (1,l-torsion+±)-signature has genus 1. -/
theorem consumer_typeOneLTorsionPlusMinus_genus (l : PrimeGeFive) :
    (typeOneLTorsionPlusMinus l).genus = 1 :=
  typeOneLTorsionPlusMinus_genus l

#check consumer_typeOneOne_genus
#check consumer_typeOneOne_punctures
#check consumer_typeOneOne_stackyOrders
#check consumer_typeOneLTorsion_genus
#check consumer_typeOneLTorsionPlusMinus_genus

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaConsumerActual
end
