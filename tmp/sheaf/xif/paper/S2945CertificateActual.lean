import tmp.sheaf.xif.paper.S2944ThetaLinkRealization
import tmp.sheaf.xif.paper.S2937AbsNormJLeQPilotActual
import tmp.sheaf.xif.paper.S2739FinsetSupportActual
import tmp.sheaf.xif.paper.S2838HeightComparisonReductionActual
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2936ThetaUpperConstantActual
open LeanFormal.IUT.XiFPaper.S2944ThetaLinkRealization
open LeanFormal.IUT.XiFPaper.S2937AbsNormJLeQPilotActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2945CertificateActual

theorem S2945_maxIdeal_ne_bot
    (p : NumberField.FinitePlace (S2735Arithmetic S2771FiveLabel).K) :
    p.maximalIdeal.asIdeal ≠ ⊥ := by
  have hmax : p.maximalIdeal.asIdeal.IsMaximal := p.maximalIdeal.isMaximal
  exact Ring.ne_bot_of_isMaximal_of_not_isField hmax
    (NumberField.RingOfIntegers.not_isField (S2735Arithmetic S2771FiveLabel).K)

theorem S2945_supportIdeal_ne_bot (a b c : Nat) :
    S2752J S2771FiveLabel a b c ≠ ⊥ := by
  unfold S2752J
  rw [show supportIdeal (K := (S2735Arithmetic S2771FiveLabel).K)
      (abcRationalPoint a c) =
      ∏ i : SupportIndex (abcRationalPoint a c),
        (supportPlace (K := (S2735Arithmetic S2771FiveLabel).K)
          (abcRationalPoint a c) i).maximalIdeal.asIdeal from rfl]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => S2945_maxIdeal_ne_bot
    (supportPlace (K := (S2735Arithmetic S2771FiveLabel).K)
      (abcRationalPoint a c) i))

theorem S2945_S2921S_nonneg (a b c : Nat) :
    0 ≤ S2921S a b c := by
  unfold S2921S
  apply Real.log_nonneg
  have hpos : 0 < Ideal.absNorm (S2752J S2771FiveLabel a b c) := by
    rw [Ideal.absNorm_pos_iff_mem_nonZeroDivisors]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (S2945_supportIdeal_ne_bot a b c)
  exact_mod_cast Nat.succ_le_of_lt hpos

theorem S2945_T_nonneg (a b c : Nat) : 0 ≤ S2921T a b c := by
  unfold S2921T
  exact mul_nonneg (by positivity) (S2945_S2921S_nonneg a b c)

/-- Full S2933 certificate with only height_le_procession explicit. -/
noncomputable def S2945Certificate
    (n : Nat) (hn : 2 ≤ n)
    (height_le_procession :
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcJInvariant a b c) ≤
          (1 / (n : Real)) *
            ∑ j ∈ Finset.Icc 1 n,
              LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
                (2 * (n : Real) + 1) S2921D
                (S2921Q a b c) (S2921S a b c) (S2921T a b c) j) :
    S2933Certificate where
  n := n
  hn := hn
  eps := S2944Eps n S2771FiveLabel.value
  AJ := S2944AJ n
  hD := fun _ _ _ => S2921D_nonneg
  hS := fun a b c => S2945_S2921S_nonneg a b c
  hT := fun a b c => S2945_T_nonneg a b c
  height_le_procession := height_le_procession
  theta_le_region := fun a b c habc =>
    S2944_theta_le_region n hn a b c habc

/-- Certificate yields S2838ThetaUpperGap. -/
theorem S2945_to_S2838ThetaUpperGap
    (n : Nat) (hn : 2 ≤ n)
    (height_le_procession :
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcJInvariant a b c) ≤
          (1 / (n : Real)) *
            ∑ j ∈ Finset.Icc 1 n,
              LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
                (2 * (n : Real) + 1) S2921D
                (S2921Q a b c) (S2921S a b c) (S2921T a b c) j) :
    S2838ThetaUpperGap (S2944Eps n S2771FiveLabel.value) (S2944AJ n) :=
  S2933_to_S2838ThetaUpperGap (S2945Certificate n hn height_le_procession)

#check S2945Certificate
#check S2945_to_S2838ThetaUpperGap
#print axioms S2945Certificate
#print axioms S2945_to_S2838ThetaUpperGap

end LeanFormal.IUT.XiFPaper.S2945CertificateActual
end
