import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-! # S690: symbolic coefficient expansion for root Theta vs qPilot

rootThetaMagnitudeValue j = (j^2/(2l)) * (order * log p).
The qPilot local magnitude is order * log p.  Hence all j^2/(2l) factors are
explicit; there is no termwise cancellation unless j^2 = 2l.  In particular the
zero label gives j^2 = 0 != 2l, so no termwise identity holds. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S690RootThetaCoefficientExpansionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual qPilot local magnitude: order(q) * log p. -/
noncomputable def qPilotLocalMagnitude : Real :=
  ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)

/-- Exact coefficient expansion: root theta magnitude is j^2/(2l) times the
qPilot local magnitude. -/
theorem rootThetaMagnitudeValue_eq_ratio_mul_qPilot
    (j : SignedLabel l.value) :
    rootThetaMagnitudeValue T b j =
      (((gaussExponent j.1).toNat : Real) / (2 * l.value : Real)) *
        qPilotLocalMagnitude T b := by
  unfold rootThetaMagnitudeValue qPilotLocalMagnitude
    qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
  simp only [qVFamTensorV, Finset.univ_unique, Finset.sum_singleton]
  ring_nf

/-- Zero label of SignedLabel, used to refute termwise cancellation. -/
def zeroSignedLabel : SignedLabel l.value :=
  ⟨0, by
    have hstar : (0 : Int) ≤ (lStar l.value : Int) := by exact_mod_cast Nat.zero_le _
    constructor <;> omega⟩

theorem zeroSignedLabel_gauss : gaussExponent (zeroSignedLabel (l := l)).1 = 0 := by
  simp [zeroSignedLabel, gaussExponent]

/-- No termwise identity j^2 = 2l can hold for every label. -/
theorem not_forall_gaussExponent_eq_twoL :
    ¬ ∀ j : SignedLabel l.value,
      gaussExponent j.1 = (2 * l.value : Int) := by
  intro h
  have h0 := h (zeroSignedLabel (l := l))
  rw [zeroSignedLabel_gauss] at h0
  have hl : (0 : Int) < (l.value : Int) := by exact_mod_cast l.prime.pos
  omega

/-- Exact missing termwise condition: only labels with j^2 = 2l could match
the qPilot magnitude without weighted cancellation. -/
def TermwiseQvPilotMatch (j : SignedLabel l.value) : Prop :=
  gaussExponent j.1 = (2 * l.value : Int)

theorem termwiseQvPilotMatch_fails_at_zero :
    ¬ TermwiseQvPilotMatch (l := l) (zeroSignedLabel (l := l)) := by
  unfold TermwiseQvPilotMatch
  rw [zeroSignedLabel_gauss]
  have hl : (0 : Int) < (l.value : Int) := by exact_mod_cast l.prime.pos
  omega

end LeanFormal.IUT.XiFPaper.S690RootThetaCoefficientExpansionActual

end
