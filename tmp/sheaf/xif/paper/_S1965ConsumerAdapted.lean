import tmp.sheaf.xif.paper.S1965FDoublePlusStripActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1965Consumer

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1965FDoublePlusStripActual

#check paperModFDoublePlus
#check paperCoricDoublePlusOfLocalMonoids
#check paperOneColumnDoublePlus
#check paperCoricDoublePlusOfLocalMonoids_rho_apply
#check paperOneColumnDoublePlus_primeEquiv

example (D : S1895PaperInput) :
    (paperModFDoublePlus D).global = paperGlobalRealifiedFrobenioid D := rfl

example (D : S1895PaperInput) (v : NumberFieldPlace (PaperFmod D)) :
    (paperModFDoublePlus D).primeEquiv v = v := rfl

example (D : S1895PaperInput) (v : NumberFieldPlace (PaperFmod D)) :
    (paperModFDoublePlus D).rho v
        (Multiplicative.ofAdd (placeComponentPrime (F := PaperFmod D) v)) =
      Multiplicative.ofAdd (1 : NNReal) :=
  paperModFDoublePlus_rho_prime D v

#print axioms paperModFDoublePlus
#print axioms paperModFDoublePlus_rho_prime
#print axioms paperCoricDoublePlusOfLocalMonoids
#print axioms paperCoricDoublePlusOfLocalMonoids_rho_apply
#print axioms paperOneColumnDoublePlus

end LeanFormal.IUT.XiFPaper.S1965Consumer
