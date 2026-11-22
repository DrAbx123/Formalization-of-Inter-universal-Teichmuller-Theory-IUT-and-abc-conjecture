import tmp.sheaf.xif.paper.W6LogLocalSystemGroupoidActual
import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual

/-!
# W6: the mu_2l indeterminacy local system on the finite root stack

This file instantiates the log-local-system/monodromy layer at the **actual**
finite root stack @L(mu_2l)@ of @S782FiniteRootStackExtensionActual@ and the
actual stacky log-volume of @S824RootStackyHaarVolumeActual@.

Three actual statements:

* @norm_stackMuUnit_eq_one@ and @stackyBallLog_mu_invariant@: the
  mu_2l-indeterminacy direction has **trivial monodromy**, i.e. the log volume
  is invariant under the mu_2l action.  This is the positive half of the W6
  proposal ("trivial monodromy => paths preserve the log") and it is exactly
  the branch independence theorem of S824;
* @not_mu_orbit_root_to_q@: the q-section and the root section are **not** in
  the same mu_2l orbit, because the mu action fixes the divisor coordinate and
  the two sections have divisor coordinates @order@ and @order/(2l)@.  So the
  Ind/mu indeterminacy alone cannot connect qPilot and Theta;
* @trivialMonodromyLink_forces_cnorm_eq_order@: if a log local system with a
  **zero monodromy** link connects the paper least-hull log to the stacky root
  log, then @c_norm = order@.  By the S824 dichotomy this is an open arithmetic
  statement (S736); hence "trivial monodromy + connectedness" is not weaker
  than the gap, it *is* the gap in the stacky normalization.

No sorry, no axiom, no fake carrier.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.W6RootStackMonodromyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.W6LogLocalSystemGroupoidActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. Trivial monodromy of the mu_2l indeterminacy -/

/-- The primitive 2l-th root of unity has norm one. -/
theorem norm_stackMuUnit_eq_one :
    ‖(stackMuUnit (l := l) T b : rootStackExtension T b)‖ = 1 := by
  have hpow : ‖(stackMuUnit (l := l) T b : rootStackExtension T b)‖₊ ^ (2 * l.value) = 1 := by
    have h := congrArg (fun u : (rootStackExtension T b)ˣ =>
      ‖(u : rootStackExtension T b)‖₊) (stackMuUnit_pow_twoL (l := l) T b)
    simpa [Units.val_pow_eq_pow_val, nnnorm_pow] using h
  have h2l : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
  have hnn : ‖(stackMuUnit (l := l) T b : rootStackExtension T b)‖₊ = 1 :=
    nnreal_pow_eq_one h2l hpow
  simpa using congrArg (fun x : NNReal => (x : Real)) hnn

/-- The stacky log-volume of the ball of radius @||u||@; this is the log-volume
of the root/q region attached to a unit. -/
noncomputable def stackyBallLog (mu : Measure (rootStackExtension T b))
    (u : (rootStackExtension T b)ˣ) : Real :=
  stackyLogVolume (l := l) T b mu
    (Metric.closedBall (0 : rootStackExtension T b)
      ‖(u : rootStackExtension T b)‖)

/-- The class of a unit modulo the mu_2l indeterminacy has the same stacky
log-volume: the mu_2l direction has trivial monodromy. -/
theorem stackyBallLog_mu_invariant (mu : Measure (rootStackExtension T b))
    [Measure.IsAddHaarMeasure mu] [mu.Regular] (u : (rootStackExtension T b)ˣ) :
    stackyBallLog (l := l) T b mu (stackMuUnit (l := l) T b * u) =
      stackyBallLog (l := l) T b mu u := by
  unfold stackyBallLog
  have hnorm : ‖((stackMuUnit (l := l) T b * u : (rootStackExtension T b)ˣ) :
      rootStackExtension T b)‖ = ‖(u : rootStackExtension T b)‖ := by
    rw [Units.val_mul, norm_mul, norm_stackMuUnit_eq_one, one_mul]
  rw [hnorm]

/-! ## 2. The mu_2l orbit does not connect q and Theta -/

/-- The mu_2l action on the finite root-stack carrier: multiply the unit part by
a power of the primitive root, leave the divisor coordinate unchanged. -/
noncomputable def muActCarrier (n : Int) (u : StackSectionCarrier T b) :
    StackSectionCarrier T b :=
  (stackMuUnit (l := l) T b ^ n * u.1, u.2)

theorem muActCarrier_snd (n : Int) (u : StackSectionCarrier T b) :
    (muActCarrier (l := l) T b n u).2 = u.2 := rfl

/-- **The q-section and the root section are not in the same mu_2l orbit when
the q-parameter is non-trivial**: the divisor coordinates are @order@ and
@order/(2l)@, and the mu action fixes that coordinate. -/
theorem not_mu_orbit_root_to_q (horder : (qVFamily T b).order ≠ 0) (n : Int) :
    muActCarrier (l := l) T b n (stackRootSection (l := l) T b) ≠
      stackQSection (l := l) T b := by
  intro h
  have h2 : (stackRootSection (l := l) T b).2 = (stackQSection (l := l) T b).2 := by
    have := congrArg Prod.snd h
    rwa [muActCarrier_snd] at this
  change Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * (l.value : Real)))
      = Multiplicative.ofAdd ((qVFamily T b).order : Real) at h2
  have hdiv : ((qVFamily T b).order : Real) / (2 * (l.value : Real)) =
      ((qVFamily T b).order : Real) := Multiplicative.ofAdd.injective h2
  have hpos : (0 : Real) < ((qVFamily T b).order : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero horder
  have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
  have h2l : (1 : Real) < 2 * (l.value : Real) := by linarith
  have hlt : ((qVFamily T b).order : Real) / (2 * (l.value : Real)) <
      ((qVFamily T b).order : Real) := div_lt_self hpos h2l
  linarith

/-! ## 3. A trivial-monodromy link forces the S736 statement -/

/-- **The exact gap.**  If a log local system has a zero-monodromy link between
an object with the paper least-hull log and an object with the degree-normalized
stacky root log, then @c_norm = order@ (S736).  So the W6 "trivial monodromy"
hypothesis is not a convenient extra structure: under the stacky normalization
it is *equivalent* to the open arithmetic statement. -/
theorem trivialMonodromyLink_forces_cnorm_eq_order
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b))
    (n : Nat) (hn : 0 < n)
    (hchar : StackCharacterNormComparison (l := l) T b n)
    {C : Type u} [Category C] (L : LogLocalSystem C) (X Y : C) (f : X ⟶ Y)
    (hX : L.val X = paperLeastLambdaOHullLog (l := l) T b mu)
    (hY : L.val Y = (1 / (n : Real)) *
      Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
        (stackRootUnit (l := l) T b) : Real))
    (hzero : L.monodromy f = 0) :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) := by
  have hval : L.val X = L.val Y := L.val_eq_of_monodromy_eq_zero f hzero
  rw [hX, hY] at hval
  exact (stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order (l := l) T b mu D n hn
    hchar).mp hval.symm

/-- Contrapositive form: if the spectral coefficient differs from the valuation
order, *no* zero-monodromy link between the two scalars exists. -/
theorem no_trivialMonodromyLink_of_cnorm_ne_order
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b))
    (n : Nat) (hn : 0 < n)
    (hchar : StackCharacterNormComparison (l := l) T b n)
    (hne : qVFamNormalizedCoefficient T b ≠ ((qVFamily T b).order : Real))
    {C : Type u} [Category C] (L : LogLocalSystem C) (X Y : C) (f : X ⟶ Y)
    (hX : L.val X = paperLeastLambdaOHullLog (l := l) T b mu)
    (hY : L.val Y = (1 / (n : Real)) *
      Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
        (stackRootUnit (l := l) T b) : Real)) :
    L.monodromy f ≠ 0 := by
  intro hzero
  exact hne (trivialMonodromyLink_forces_cnorm_eq_order (l := l) T b mu D n hn hchar
    L X Y f hX hY hzero)

end LeanFormal.IUT.XiFPaper.W6RootStackMonodromyActual
