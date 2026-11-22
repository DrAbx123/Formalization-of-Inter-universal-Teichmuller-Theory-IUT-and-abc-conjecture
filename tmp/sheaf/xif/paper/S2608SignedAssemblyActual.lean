import tmp.sheaf.xif.paper.S2607SignedGapActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2607SignedGapActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2608SignedAssemblyActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (j : SignedLabel l.value)

/-- Conditional assembly: signed gap1 + SignedGap2Target + a selector `epsOf`
with `(1+eps)^2 <= 1+eps'` gives the IUT IV Theorem A additive contract. -/
theorem ABCHeightWeightAdditiveBoundV2_of_signedGaps
    (epsOf : Real -> Real) (Aeps D0 D1 : Real -> Real)
    (heps : forall e : Real, 0 < e -> 0 < epsOf e)
    (hsel : forall e : Real, 0 < e -> (1 + epsOf e) ^ 2 <= 1 + e)
    (hA : forall e : Real, 0 < e -> 0 <= Aeps e)
    (hval : forall e : Real, 0 < e ->
      forall a b c : Nat, IsABCTriple a b c ->
        forall p, p ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
          max 0 (-(padicValRat p (abcRationalPoint a c) : Real)) <=
            1 + epsOf e)
    (hweight : forall e : Real, 0 < e ->
      forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          (SignedVolume I v {I.sourceThetaPilotPoint v R n j}).toReal)
    (hgap2 : forall e : Real, 0 < e ->
      SignedGap2Target I v R n {I.sourceThetaPilotPoint v R n j} j (epsOf e) (D0 e) (D1 e)) :
    ABCHeightWeightAdditiveBoundV2 := by
  intro e he
  let eps := epsOf e
  have hvc := signedGap1_height I v R n j (le_of_lt (heps e he)) (hA e he)
    (hval e he) (hweight e he)
  have hv := hgap2 e he
  refine ⟨(1 + eps) *
      ((SignedVolume I v {I.sourceThetaPilotPoint v R n j}).toReal + D0 e + D1 e) + Aeps e, ?_⟩
  intro a b c habc
  have h1 := hvc a b c habc
  have h2 := hv a b c habc
  simp only [Set.union_self] at h2
  have hsquare : (1 + eps) * (1 + eps) <= 1 + e := by
    simpa [pow_two] using hsel e he
  have hw : 0 <= arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  have hvol : 0 <= (SignedVolume I v {I.sourceThetaPilotPoint v R n j}).toReal :=
    ENNReal.toReal_nonneg
  nlinarith [h1, h2, hsquare, hw, hvol, le_of_lt (heps e he)]

#print axioms ABCHeightWeightAdditiveBoundV2_of_signedGaps

end LeanFormal.IUT.XiFPaper.S2608SignedAssemblyActual
end
