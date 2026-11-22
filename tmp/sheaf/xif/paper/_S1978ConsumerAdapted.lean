import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.IPLAPTDataActual

noncomputable section
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual

namespace LeanFormal.IUT.XiFPaper.S1978Consumer

-- the actual non-torsion unit 1+5
example : ¬ IsOfFinOrder (@localOFieldUnit 5 ⟨Nat.prime_five⟩) :=
  @localOFieldUnit_not_isOfFinOrder 5 ⟨Nat.prime_five⟩

-- the actual local O^×μ quotient is nontrivial
example :
    (TimesMuQuotient.quotientMap
      (@localOFieldUnit 5 ⟨Nat.prime_five⟩) :
      @LocalOFieldUnitsMu 5 ⟨Nat.prime_five⟩) ≠ 1 :=
  @LocalOFieldUnitsMu_nontrivial 5 ⟨Nat.prime_five⟩

-- the local strip's value monoid is the actual O^× group
example : localOFieldStrip.Mon s1895FivePlace =
    @LocalOFieldUnits 5 ⟨Nat.prime_five⟩ := rfl

-- no equivalence to the S1895 paper object's strip
example (D : S1895PaperInput) :
    ¬ Nonempty (FPrimeStripEquiv localOFieldStrip (S1895PaperO D).strip) :=
  no_localOFieldStrip_equiv_paperO D

-- the related paper object exists and its strip is the local strip
example (D : S1895PaperInput) :
    (localOFieldPaperO D).strip = localOFieldStrip := rfl

example (D : S1895PaperInput) :
    (localOFieldPaperO D).strip =
      sourceQPilotStrip (localOFieldPaperO D).boundary := rfl

-- the exact missing bridge is impossible
example (D : S1895PaperInput) :
    ¬ Nonempty (S1978FirstMissingBridge D) :=
  S1978FirstMissingBridge_impossible D

end LeanFormal.IUT.XiFPaper.S1978Consumer
