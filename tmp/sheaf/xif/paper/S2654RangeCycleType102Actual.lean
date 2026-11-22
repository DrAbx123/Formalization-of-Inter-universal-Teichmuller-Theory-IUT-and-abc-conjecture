import tmp.sheaf.xif.paper.S2653DedekindToRangeActual
import tmp.sheaf.xif.paper.S2494bRootCycleTypeMod29Actual

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2654RangeCycleType102Actual

variable (f : (RingOfIntegers S1720Field)[X])
  (p : Ideal (RingOfIntegers S1720Field)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers S2057FiveDivisionField)) [hP : P.IsPrime]
  [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers S1720Field)
    S2057FiveDivisionField)).Splits)
  (σ : Gal(S2057FiveDivisionField/S1720Field))
  (H : @IsArithFrobAt (RingOfIntegers S1720Field)
    (RingOfIntegers S2057FiveDivisionField) _ _ _
    Gal(S2057FiveDivisionField/S1720Field) _
    (LeanFormal.IUT.XiFPaper.S2494bRootCycleTypeMod29Actual.instMulSemiringActionAlgEquivRingOfIntegers_tmp S1720Field
      S2057FiveDivisionField)
    (LeanFormal.IUT.XiFPaper.S2494bRootCycleTypeMod29Actual.instSMulCommClassAlgEquivRingOfIntegers_tmp S1720Field
      S2057FiveDivisionField) σ P)
  {c : S1720Field} (hc : c ≠ 0)
  (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
    C c * S2057Psi5F)
  (hfac : factorDegrees (fbar f p) = ({2, 10} : Multiset ℕ))

include hp hP hPover hmonic hsep hsplit H hc hq hfac in
theorem S2654RangeCycleType102 :
    S2203RangeCycleTypeRequired S1982Basis := by
  have hcyc : rootCycleType S1720Field S2057FiveDivisionField f hsplit σ =
      ({10, 2} : Multiset ℕ) := by
    have h := LeanFormal.IUT.XiFPaper.S2494bRootCycleTypeMod29Actual.S2494b_rootCycleType_2_10
      S1720Field S2057FiveDivisionField f p P hmonic hsep hsplit σ H hfac
    simpa [show ({2, 10} : Multiset ℕ) = {10, 2} from by decide] using h
  exact S2653RangeTransport f p P hmonic hsep hsplit σ hc hq H hcyc

#check S2654RangeCycleType102
#print axioms S2654RangeCycleType102

end LeanFormal.IUT.XiFPaper.S2654RangeCycleType102Actual
end
