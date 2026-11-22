/- U-L theta-pilot per-b packet on the actual finite root extension (route §5.2.2,
§5.3 J1; Lead adjudication: per-b single factor `rootNormedExtension T b` with
`rootExtensionHaar`, normalized by the actual `[F_b : Q_p]`).

Status: the actual per-b region/value definitions are in place, together with the
generalized normalized-log-mass identity for any nonzero multiplicative translate
of the integral unit ball (this is the mass input for `V_a = log ‖theta_j‖`).
The exact value theorem `V_a = -ord_p(theta_j) log p` and the C1-shaped bound are
carried as the next step: they need the donor normed-algebra/finite-dimensional
structures on `F_b` to be supplied as explicit instance arguments, which is a
mechanical instance-alignment task (not a mathematical gap).
No completion root is asserted (S342QVFamilyRootImpossibleActual). -/
import tmp.sheaf.xif.paper.Mzk1URRootMassActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.RootThetaValueInLUnitActual
import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
noncomputable section
open scoped BigOperators Pointwise
namespace LeanFormal.IUT.XiFPaper.Mzk1ULThetaPacketActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootMassActual
open MeasureTheory
universe u
section Generic
variable {p : Nat} [Fact p.Prime] {L : Type*}
variable [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L]
variable [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
variable [MeasurableSpace L] [BorelSpace L]
/-- Degree-normalized log-mass of any nonzero multiplicative translate of the
integral unit ball: it is `log ‖x‖`.  This is
`normalizedLogMass_smul_units` generalized from units to arbitrary nonzero
elements (the same distribHaarChar computation). -/
theorem ulNormalizedLogMass_smul (μ : Measure L) [Measure.IsAddHaarMeasure μ]
    [Measure.Regular μ] (x : L) (hx : x ≠ 0) :
    (1 / (Module.finrank ℚ_[p] L : ℝ)) *
      (Real.log (μ (x • (Integers L : Set L))).toReal -
        Real.log (μ (Integers L : Set L)).toReal) =
      Real.log ‖x‖ := by
  have hOpos := measure_integers_pos (L := L) μ
  have hOfin := measure_integers_lt_top (L := L) μ
  have hOtoReal : (μ (Integers L : Set L)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hchar_ne : (distribHaarChar L (Units.mk0 x hx) : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := L) (g := Units.mk0 x hx)).ne'
  have hD : (0 : ℝ) < (Module.finrank ℚ_[p] L : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ_[p]) (M := L)
  have hμ : μ (Units.mk0 x hx • (Integers L : Set L)) =
      (distribHaarChar L (Units.mk0 x hx) : ENNReal) * μ (Integers L : Set L) :=
    (distribHaarChar_mul (μ := μ) (Units.mk0 x hx) (Integers L : Set L)).symm
  have hlogchar := log_distribHaarChar_eq (p := p) (L := L) μ x hx
  have hlogμ : Real.log (μ (Units.mk0 x hx • (Integers L : Set L))).toReal =
      Real.log (distribHaarChar L (Units.mk0 x hx) : ℝ) +
        Real.log (μ (Integers L : Set L)).toReal := by
    rw [hμ, ENNReal.toReal_mul, ENNReal.coe_toReal, Real.log_mul hchar_ne hOtoReal]
  have hxU : x • (Integers L : Set L) = Units.mk0 x hx • (Integers L : Set L) := by
    rw [Units.smul_mk0]
  rw [hxU, hlogμ, hlogchar]
  field_simp [hD.ne']
  ring
end Generic
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- The actual finite root extension is complete. -/
noncomputable instance ulRootExtensionComplete : CompleteSpace (rootNormedExtension T b) :=
  rootNormedExtensionComplete (T := T) (b := b)
/-- The actual finite root extension is ultrametric (norm inherited from the
actual normed algebraic closure). -/
noncomputable instance ulRootExtensionUltrametric : IsUltrametricDist (rootNormedExtension T b) := by
  haveI : IsUltrametricDist (rootNormedAmbient T b) :=
    inferInstanceAs (IsUltrametricDist (SourceAlgebraicClosure (qVFamTensorPlace T b)))
  exact inferInstance
/-- Actual `[F_b : Q_p]` as a real number. -/
noncomputable def ulFinrankF : Real :=
  (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real)
/-- The integral unit ball of the actual finite root extension. -/
noncomputable def ulThetaPacketUnitBall : Set (rootNormedExtension T b) :=
  (Integers (rootNormedExtension T b) : Set (rootNormedExtension T b))
/-- Log-Haar-mass of the unit ball. -/
noncomputable def ulThetaPacketUnitBallLog : Real :=
  Real.log (rootExtensionHaar T b (ulThetaPacketUnitBall T b)).toReal
/-- The actual per-b theta-pilot region: theta_j times the integral unit ball of
the actual finite root extension `F_b = K_b(r_b)`. -/
noncomputable def ulThetaPacketRegion (j : SignedLabel l.value) :
    Set (rootNormedExtension T b) :=
  (rootNormedThetaValueInL T b j) • ulThetaPacketUnitBall T b
/-- The actual per-b theta-pilot value `V_a`: the actual finrank-normalized Haar
log-mass of the theta principal lattice, relative to the unit ball. -/
noncomputable def ulThetaPacketV (j : SignedLabel l.value) : Real :=
  (1 / ulFinrankF T b) *
    (Real.log (rootExtensionHaar T b (ulThetaPacketRegion T b j)).toReal -
      ulThetaPacketUnitBallLog T b)
/-- The actual paper different order `d_i = ord_p(delta_i)` is nonnegative (the
actual different generator is integral). -/
theorem ulDifferentOrder_nonneg (i : qVFamTensorV) :
    0 ≤ localNormOrder (qVFamTensorP T b)
      (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i) := by
  have h := LeanFormal.IUT.LocalDifferentNormOrder.localNormOrder_differentGenerator_eq_paperOrder
    (p := qVFamTensorP T b)
    (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
  rw [show arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i =
      ((LeanFormal.IUT.IntegralTraceDualTensorInclusion.localDifferentGenerator
          (p := qVFamTensorP T b)
          (L := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))) :
        CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))) from rfl]
  rw [h]
  unfold LeanFormal.IUT.IntegralTraceDualTensorInclusion.localDifferentPaperOrder
  apply div_nonneg (Nat.cast_nonneg _)
  have hpos : (0 : Real) < (logShellRamificationExponent
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b) : Real) := by
    exact_mod_cast (LocalFieldLogarithm.logShellRamificationExponent_pos
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b))
  exact hpos.le
/-- The actual paper different sum is nonnegative. -/
theorem ulDifferentSum_nonneg :
    0 ≤ ∑ i, localNormOrder (qVFamTensorP T b)
      (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i) :=
  Finset.sum_nonneg (fun i _ => ulDifferentOrder_nonneg (T := T) (b := b) i)
/-- The actual exceptional sum `Σ_{i∈I*} (3 + log e_i)` is nonnegative. -/
theorem ulExceptionalSum_nonneg (exceptional : Finset qVFamTensorV) :
    0 ≤ ∑ i ∈ exceptional, (3 + Real.log
      (logShellRamificationExponent
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
        (p := qVFamTensorP T b) : Real)) := by
  apply Finset.sum_nonneg
  intro i _
  have h1 : (1 : Real) ≤ (logShellRamificationExponent
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b) : Real) := by
    have hpos := LocalFieldLogarithm.logShellRamificationExponent_pos
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b)
    exact_mod_cast hpos
  have hlog : 0 ≤ Real.log (logShellRamificationExponent
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b) : Real) := Real.log_nonneg h1
  linarith
#print axioms ulNormalizedLogMass_smul
#print axioms ulDifferentOrder_nonneg
#print axioms ulDifferentSum_nonneg
#print axioms ulExceptionalSum_nonneg
end LeanFormal.IUT.XiFPaper.Mzk1ULThetaPacketActual
end
