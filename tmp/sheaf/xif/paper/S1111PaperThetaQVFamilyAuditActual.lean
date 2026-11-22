import tmp.sheaf.xif.paper.TwoLthRootKummerActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-! # S1111: audit of actualSignedC3 (fixed q=1/5) versus qVFamily q_v theta

Existing actual files:
* C3GaussianThetaPacketActual: actualGaussianThetaPacket uses gaussianFiveThetaQ
  (q = 1/5) and actualSignedC3 is definitionally this Gaussian C3.
* TwoLthRootKummerActual: actual 2l-th root hodgeTwoLthRoot of qVFamily q_v in
  the algebraic closure, with hodgeTwoLthRoot^(2l) = q_v.
* QVFamRootFactorCorrectionActual: paper theta value
  qVFamPaperThetaValueRoot j = hodgeTwoLthRoot^(j^2), coefficient
  j^2 * order(q_v)/(2l).

Thus the existing qVFamily theta data are actual and use q_v^(j^2/2l); the
existing actualSignedC3 uses the fixed Gaussian q=1/5.  No equality between
them is in the tree.  This file proves the actual q_v theta power relation and
records the exact bridge to the fixed 1/5 theta data. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1111PaperThetaQVFamilyAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u ua uv upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual qVFamily theta value power: (q_v^(j^2/2l))^(2l) = q_v^(j^2). -/
theorem s1111QVThetaValue_pow (j : SignedLabel l.value) :
    qVFamPaperThetaValueRoot (l := l) T b j ^ (2 * l.value) =
      qVAlgClosedUnit (l := l) T b ^ (gaussExponent j.1).toNat := by
  unfold qVFamPaperThetaValueRoot qVAlgClosedUnit
  rw [← pow_mul, Nat.mul_comm ((gaussExponent j.1).toNat) (2 * l.value),
    pow_mul, hodgeTwoLthRoot_pow]

/-- The actual qVFamily theta coefficient is j^2 * order(q_v)/(2l). -/
theorem s1111QVThetaCoefficient (j : SignedLabel l.value) :
    qVFamPaperThetaTensorCoefficient (l := l) T b j =
      ((gaussExponent j.1).toNat : Real) * qVFamPaperRootCoefficient (l := l) T b := rfl

/-- Exact bridge: the qVFamily theta data are the fixed 1/5 Gaussian theta data
only if the q_v root matches the fixed root.  This is not provable for an
arbitrary bad place b. -/
def S1111QVThetaMatchesOneFifth
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  ∃ r : (AlgebraicClosure (Completion (qVPlace T b)))ˣ,
    r ^ (2 * l.value) = qVAlgClosedUnit (l := l) T b ∧
      ∀ j : SignedLabel l.value, qVFamPaperThetaValueRoot (l := l) T b j =
        r ^ (gaussExponent j.1).toNat

/-- Exact minimal bridge to the fixed Gaussian theta packet. -/
def S1111ExactMinimum
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  S1111QVThetaMatchesOneFifth T b

end LeanFormal.IUT.XiFPaper.S1111PaperThetaQVFamilyAuditActual

end
