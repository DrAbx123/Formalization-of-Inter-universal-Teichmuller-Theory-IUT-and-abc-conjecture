import tmp.sheaf.xif.paper.S530EtThQSqrtRecipeSpecActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

-- S531: actual theta-unit candidate in ACF, qHalf=theta^l, mu2l action.
-- Evaluation splitting/normalization remains exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S531EtThThetaUnitRecipeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual
open LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual
open LeanFormal.IUT.XiFPaper.S530EtThQSqrtRecipeSpecActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def thetaUnitElement : ACF T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (qUnit T b : ACF T b) (n := 2 * l.value)
      (Nat.mul_pos (by norm_num) l.prime.pos))

theorem thetaUnitElement_pow :
    thetaUnitElement T b ^ (2 * l.value) = (qUnit T b : ACF T b) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (qUnit T b : ACF T b) (Nat.mul_pos (by norm_num) l.prime.pos))

theorem thetaUnitElement_ne_zero : thetaUnitElement T b ≠ 0 := by
  intro h
  have hpow := thetaUnitElement_pow T b
  rw [h, zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow
  exact (Units.ne_zero (qUnit T b)) hpow.symm

noncomputable def thetaUnitCandidate : (ACF T b)ˣ :=
  Units.mk0 (thetaUnitElement T b) (thetaUnitElement_ne_zero T b)

theorem thetaUnitCandidate_pow :
    thetaUnitCandidate T b ^ (2 * l.value) = qUnit T b := by
  ext
  simpa [thetaUnitCandidate] using thetaUnitElement_pow T b
noncomputable def qHalfUnitCandidate : (ACF T b)ˣ :=
  thetaUnitCandidate T b ^ l.value

theorem qHalfUnitCandidate_eq :
    qHalfUnitCandidate T b = thetaUnitCandidate T b ^ l.value := rfl

theorem qHalfUnitCandidate_sq :
    qHalfUnitCandidate T b ^ 2 = qUnit T b := by
  rw [qHalfUnitCandidate_eq, ← pow_mul, show l.value * 2 = 2 * l.value by ring]
  exact thetaUnitCandidate_pow T b

noncomputable def thetaLabelUnit (j : SignedLabel l.value) : (ACF T b)ˣ :=
  thetaUnitCandidate T b ^ (gaussExponent j.1).toNat

noncomputable def mu2lThetaAction
    (ζ : rootsOfUnity (2 * l.value) (ACF T b)) : (ACF T b)ˣ :=
  ζ * thetaUnitCandidate T b

-- Exact missing evaluation-section data: no repo evaluation section at the
-- special 2-torsion point; hence no splitting/normalization proof.
structure ThetaEvaluationSplittingGap where
  evalSection : ConversePoint T b → ACF T b
  evalSection_special : Prop
  splitting_equivariant : Prop
  kummerClass_eq_theta_pow : Prop
  normalization_by_special_point : Prop

#check thetaUnitCandidate
#check thetaUnitCandidate_pow
#check qHalfUnitCandidate_sq
#check thetaLabelUnit
#check mu2lThetaAction
#check ThetaEvaluationSplittingGap

end LeanFormal.IUT.XiFPaper.S531EtThThetaUnitRecipeActual

end