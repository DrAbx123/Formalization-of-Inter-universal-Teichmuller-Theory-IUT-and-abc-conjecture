import LeanFormal.IUT.Foundations.Geometry.TateCurveLocalReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.TateCurvePadic
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2691CanonicalMultiplicativeCertificateActual

local instance s2691FivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The prime label `5`. -/
def l5 : PrimeGeFive where
  value := 5
  prime := by decide
  ge_five := by norm_num

/-- Canonical multiplicative certificate at `l = 5`, directly from the actual
TateCurveLocalReduction certificate. -/
def S2691Certificate :
    TateCurve.MultiplicativeCertificate ℤ_[5]
      (TateCurve.weierstrassCurve ℚ_[5] 5) :=
  letI : Fact (Nat.Prime l5.value) := l5.factPrime
  canonicalMultiplicativeCertificate l5

/-- The coordinate change of the certificate is `1`. -/
theorem S2691Certificate_coordinateChange :
    S2691Certificate.coordinateChange = 1 := rfl

/-- The transformed curve is exactly the target Tate curve. -/
theorem S2691Certificate_transformed :
    S2691Certificate.transformed =
      TateCurve.weierstrassCurve ℚ_[5] 5 :=
  letI : Fact (Nat.Prime l5.value) := l5.factPrime
  canonicalMultiplicativeCertificate_transformed l5

theorem S2691Certificate_multiplicative :
    HasMultiplicativeReductionOnMinimalModel ℤ_[5]
      (TateCurve.weierstrassCurve ℚ_[5] 5) :=
  S2691Certificate.hasMultiplicativeReductionOnMinimalModel

theorem S2691Certificate_stable :
    TateCurve.HasStableReductionOnMinimalModel ℤ_[5]
      (TateCurve.weierstrassCurve ℚ_[5] 5) :=
  TateCurve.multiplicative_certificate_stable (R := ℤ_[5]) S2691Certificate

#check S2691Certificate
#check S2691Certificate_transformed

end LeanFormal.IUT.XiFPaper.S2691CanonicalMultiplicativeCertificateActual
end