import tmp.sheaf.xif.paper.S2061BaseCompletionGaloisActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace S2061Consumer

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S2061BaseCompletionGaloisActual
open LeanFormal.IUT.XiFPaper.S2047GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.S2046OperationComponentsActual

variable (v : FinitePrimePlace 2 7)
local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

example : S2047BaseModelEquivRequired (v := v) := S2061S2047BaseModelEquiv v
example : S2047RationalCompletionModelEquiv (v := v) := S2061RationalCompletionModelEquiv v
example : S2047GaloisEquivOfBaseData (v := v) := S2061S2047GaloisEquivOfBaseData v
example : S2047GaloisEquivRequired (v := v) := S2061S2047GaloisEquivRequired v
example : S2046GaloisEquivRequired (v := v) := S2061S2046GaloisEquivRequired v

#check S2061S2047BaseModelEquiv
#check S2061RationalCompletionModelEquiv
#check S2061S2047GaloisEquivOfBaseData
#check S2061S2047GaloisEquivRequired

#print axioms S2061S2047BaseModelEquiv
#print axioms S2061RationalCompletionModelEquiv
#print axioms S2061S2047GaloisEquivOfBaseData
#print axioms S2061S2047GaloisEquivRequired
#print axioms S2061S2046GaloisEquivRequired

end S2061Consumer
end
