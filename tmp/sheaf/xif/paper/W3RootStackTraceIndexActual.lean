import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# W3: the mu_{2l} trace/Jones-index normalization on the finite root stack

Task H left the reading "the paper log is already a trace, and 1/(2l) is the
Jones index" as prose (S732_NCG_ROUTE_MEMO, P2).  This file upgrades the
*normalization* part to a compiled statement on the actual S782 finite
root-stack carrier and the actual S793 least lambda-O hull.

No paper inequality is asserted.  The literal identification
"least hull log = the trace/index constant" is false unless q.order = 1;
the exact criterion is proved below.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.W3RootStackTraceIndexActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open MeasureTheory

/-! ## 1. The finite mu_{2l} fiber -/

/-- The order of the finite root-stack group mu_{2l}. -/
def rootStackIndex (l : PrimeGeFive) : Nat := 2 * l.value

theorem rootStackIndex_pos (l : PrimeGeFive) : 0 < rootStackIndex l := by
  unfold rootStackIndex
  exact Nat.mul_pos (by norm_num) l.prime.pos

theorem rootStackIndex_ne_zero (l : PrimeGeFive) : rootStackIndex l ≠ 0 :=
  Nat.ne_of_gt (rootStackIndex_pos l)

theorem rootStackIndex_ge_two (l : PrimeGeFive) : 2 ≤ rootStackIndex l := by
  unfold rootStackIndex
  have h : 5 ≤ l.value := l.ge_five
  omega

instance rootStackIndexNeZero (l : PrimeGeFive) : NeZero (rootStackIndex l) :=
  ⟨rootStackIndex_ne_zero l⟩

/-- Counting trace on the finite fiber mu_{2l}. -/
noncomputable def stackFiberTrace (l : PrimeGeFive)
    (f : ZMod (rootStackIndex l) → ℝ) : ℝ :=
  ∑ a : ZMod (rootStackIndex l), f a

/-- Normalized trace tau = (1/|G|) Tr on the finite fiber. -/
noncomputable def stackFiberNormalizedTrace (l : PrimeGeFive)
    (f : ZMod (rootStackIndex l) → ℝ) : ℝ :=
  (1 / (rootStackIndex l : ℝ)) * stackFiberTrace l f

theorem stackFiberTrace_one (l : PrimeGeFive) :
    stackFiberTrace l (fun _ => (1 : ℝ)) = (rootStackIndex l : ℝ) := by
  unfold stackFiberTrace
  simp [ZMod.card]

theorem stackFiberNormalizedTrace_one (l : PrimeGeFive) :
    stackFiberNormalizedTrace l (fun _ => (1 : ℝ)) = 1 := by
  unfold stackFiberNormalizedTrace
  rw [stackFiberTrace_one]
  have h : (rootStackIndex l : ℝ) ≠ 0 := by
    exact_mod_cast rootStackIndex_ne_zero l
  field_simp [h]

/-! ## 2. The regular representation and its trace character -/

/-- Translation by a on the finite group mu_{2l}, as a permutation. -/
noncomputable def regularPerm (l : PrimeGeFive) (a : ZMod (rootStackIndex l)) :
    Equiv.Perm (ZMod (rootStackIndex l)) where
  toFun x := a + x
  invFun x := -a + x
  left_inv x := by simp
  right_inv x := by simp

theorem fixedPoints_regularPerm (l : PrimeGeFive) (a : ZMod (rootStackIndex l)) :
    Function.fixedPoints (regularPerm l a) =
      if a = 0 then (Set.univ : Set (ZMod (rootStackIndex l))) else ∅ := by
  by_cases ha : a = 0
  · ext x
    simp [Function.mem_fixedPoints, regularPerm, ha, Function.IsFixedPt]
  · ext x
    simp only [Function.mem_fixedPoints, regularPerm, ha, if_false,
      Set.mem_empty_iff_false]
    constructor
    · intro h
      have h' : a + x = (0 : ZMod (rootStackIndex l)) + x := by
        rw [zero_add]
        exact h
      exact ha (add_right_cancel h')
    · intro h
      exact False.elim h

/-- The matrix trace of the regular representation at group element a:
2l at the identity, 0 elsewhere. -/
theorem matrixTrace_regularPerm (l : PrimeGeFive) (a : ZMod (rootStackIndex l)) :
    Matrix.trace ((regularPerm l a).permMatrix ℝ) =
      if a = 0 then (rootStackIndex l : ℝ) else 0 := by
  rw [Matrix.trace_permutation, fixedPoints_regularPerm]
  by_cases ha : a = 0
  · simp [ha, Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
  · simp [ha]

/-- The permutation trace character is the delta function at the identity,
up to the index: Tr(1) = 2l, Tr(g) = 0 for g != 1. -/
theorem traceCharacter_eq_delta (l : PrimeGeFive) (a : ZMod (rootStackIndex l)) :
    Matrix.trace ((regularPerm l a).permMatrix ℝ) =
      (rootStackIndex l : ℝ) * (if a = 0 then (1 : ℝ) else 0) := by
  rw [matrixTrace_regularPerm]
  by_cases ha : a = 0 <;> simp [ha]

/-- The Jones index of the fixed-point inclusion: the trace of the identity
of the regular representation, equivalently the group order 2l. -/
noncomputable def jonesIndex (l : PrimeGeFive) : Nat := rootStackIndex l

/-- The reciprocal Jones index, i.e. the normalized trace of the identity. -/
noncomputable def jonesNormalization (l : PrimeGeFive) : ℝ :=
  1 / (jonesIndex l : ℝ)

theorem jonesIndex_eq_trace_one (l : PrimeGeFive) :
    (jonesIndex l : ℝ) = stackFiberTrace l (fun _ => (1 : ℝ)) := by
  unfold jonesIndex
  rw [stackFiberTrace_one]

theorem jonesNormalization_eq_inv_trace_one (l : PrimeGeFive) :
    jonesNormalization l = (stackFiberTrace l (fun _ => (1 : ℝ)))⁻¹ := by
  unfold jonesNormalization jonesIndex
  rw [stackFiberTrace_one, one_div]

theorem jonesIndex_eq_two_mul (l : PrimeGeFive) :
    jonesIndex l = 2 * l.value := rfl

theorem jonesNormalization_eq_inv_index (l : PrimeGeFive) :
    jonesNormalization l = ((jonesIndex l : ℝ))⁻¹ := by
  unfold jonesNormalization
  rw [one_div]

theorem jonesNormalization_pos (l : PrimeGeFive) : 0 < jonesNormalization l := by
  unfold jonesNormalization jonesIndex
  exact one_div_pos.mpr (by exact_mod_cast rootStackIndex_pos l)

/-! ## 3. The fundamental-domain function and the S782 root section -/

/-- The q divisor concentrated on a fundamental domain of the mu_{2l} fiber. -/
noncomputable def fundamentalQFunction (l : PrimeGeFive) (q : ℝ) :
    ZMod (rootStackIndex l) → ℝ :=
  fun a => if a = 0 then q else 0

theorem stackFiberTrace_fundamentalQ (l : PrimeGeFive) (q : ℝ) :
    stackFiberTrace l (fundamentalQFunction l q) = q := by
  unfold stackFiberTrace fundamentalQFunction
  simp

theorem stackFiberNormalizedTrace_fundamentalQ (l : PrimeGeFive) (q : ℝ) :
    stackFiberNormalizedTrace l (fundamentalQFunction l q) =
      q / (rootStackIndex l : ℝ) := by
  unfold stackFiberNormalizedTrace
  rw [stackFiberTrace_fundamentalQ]
  have hn : (rootStackIndex l : ℝ) ≠ 0 := by
    exact_mod_cast rootStackIndex_ne_zero l
  field_simp [hn]


section S782

variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The S782 q section's divisor coordinate is the q order. -/
theorem stackQSection_toAdd :
    Multiplicative.toAdd (stackQSection (l := l) T b).2 =
      ((qVFamily T b).order : ℝ) := rfl

/-- The S782 root section's divisor coordinate is q.order/(2l). -/
theorem stackRootSection_toAdd :
    Multiplicative.toAdd (stackRootSection (l := l) T b).2 =
      ((qVFamily T b).order : ℝ) / (rootStackIndex l : ℝ) := by
  unfold stackRootSection rootStackIndex
  push_cast
  rfl

/-- **Trace/index dictionary on the actual root section.**  The root divisor
is the normalized trace of the q divisor concentrated on a fundamental
domain. -/
theorem stackRootSection_toAdd_eq_normalizedTrace_qOrder :
    Multiplicative.toAdd (stackRootSection (l := l) T b).2 =
      stackFiberNormalizedTrace l
        (fundamentalQFunction l ((qVFamily T b).order : ℝ)) := by
  rw [stackRootSection_toAdd, stackFiberNormalizedTrace_fundamentalQ]

/-- The q section divisor is the unnormalized trace of the same fundamental
domain function. -/
theorem stackQSection_toAdd_eq_trace_qOrder :
    Multiplicative.toAdd (stackQSection (l := l) T b).2 =
      stackFiberTrace l
        (fundamentalQFunction l ((qVFamily T b).order : ℝ)) := by
  rw [stackQSection_toAdd, stackFiberTrace_fundamentalQ]

/-- qSection = (rootSection) ^ (2l) in S782, restated with the index. -/
theorem stackRootSection_pow_index :
    stackRootSection (l := l) T b ^ rootStackIndex l =
      stackQSection (l := l) T b := by
  unfold rootStackIndex
  exact stackRootSection_pow T b

/-- The actual primitive mu_{2l} unit of S782 has index-th power one, so the
finite group action factors through ZMod (2l). -/
theorem stackMuUnit_pow_index :
    stackMuUnit (l := l) T b ^ rootStackIndex l = 1 := by
  ext
  unfold rootStackIndex
  simpa [stackMuUnit] using stackMuRoot_pow T b

/-- The mu_{2l} action of S782 fixes the divisor coordinate. -/
theorem stackMuAction_divisor (u : StackSectionCarrier T b) :
    (stackMuAction T b u).2 = u.2 := rfl

/-- The coefficient form of qSection = rootSection ^ (2l):
the q coefficient is the index times the root coefficient. -/
theorem qCoefficient_eq_index_mul_rootCoefficient :
    qVFamTensorCoefficient T b =
      (rootStackIndex l : ℝ) * qVFamPaperRootCoefficient T b := by
  rw [qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient]
  unfold rootStackIndex
  norm_num

end S782

/-! ## 4. The S793 least lambda-O hull at the root-section divisor -/

section S793

variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The paper coefficient family of the least lambda-O hull is the S782
root-section divisor. -/
theorem paperRootCoefficientFamily_eq_rootSection_toAdd
    (i : qVFamTensorV) :
    paperRootCoefficientFamily (l := l) T b i =
      Multiplicative.toAdd (stackRootSection (l := l) T b).2 := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  rw [stackRootSection_toAdd]
  unfold rootStackIndex
  push_cast
  rfl

/-- **The S793 least lambda-O hull is the lambda-O region at the
mu_{2l}-normalized q divisor.** -/
theorem paperLeastLambdaOHull_eq_lambdaO_rootSection :
    paperLeastLambdaOHull (l := l) T b =
      paperLambdaORegion (l := l) T b
        (fun _ => Multiplicative.toAdd (stackRootSection (l := l) T b).2) := by
  rw [paperLeastLambdaOHull_eq_minimal]
  rfl

/-- The scaling family of the least hull is the normalized trace of the
fundamental-domain q divisor. -/
theorem paperLeastHullScaling_eq_normalizedTrace_qOrder :
    (fun _ : qVFamTensorV => qVFamPaperRootCoefficient T b) =
      fun _ => stackFiberNormalizedTrace l
        (fundamentalQFunction l ((qVFamily T b).order : ℝ)) := by
  funext i
  calc qVFamPaperRootCoefficient T b
      = paperRootCoefficientFamily (l := l) T b i := rfl
    _ = Multiplicative.toAdd (stackRootSection (l := l) T b).2 :=
        paperRootCoefficientFamily_eq_rootSection_toAdd (l := l) T b i
    _ = stackFiberNormalizedTrace l
        (fundamentalQFunction l ((qVFamily T b).order : ℝ)) :=
        stackRootSection_toAdd_eq_normalizedTrace_qOrder (l := l) T b

end S793

/-! ## 5. Exact scalar comparison and no-go criterion -/

section Comparison

variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The trace-normalized root coefficient is at most the q coefficient. -/
theorem leastHullCoefficient_le_qCoefficient :
    qVFamPaperRootCoefficient T b ≤ qVFamTensorCoefficient T b := by
  rw [qCoefficient_eq_index_mul_rootCoefficient]
  have hroot : 0 ≤ qVFamPaperRootCoefficient T b := by
    unfold qVFamPaperRootCoefficient
    positivity
  have hidx : (1 : ℝ) ≤ (rootStackIndex l : ℝ) := by
    exact_mod_cast (show 1 ≤ rootStackIndex l by
      have := rootStackIndex_ge_two l
      omega)
  calc
    qVFamPaperRootCoefficient T b = 1 * qVFamPaperRootCoefficient T b := by ring
    _ ≤ (rootStackIndex l : ℝ) * qVFamPaperRootCoefficient T b :=
      mul_le_mul_of_nonneg_right hidx hroot

/-- The exact index correction in the logarithms. -/
theorem leastHullCoefficientLog_eq_qCoefficientLog_add_log_index :
    -Real.log (qVFamPaperRootCoefficient T b) =
      -Real.log ((qVFamily T b).order : ℝ) +
        Real.log (rootStackIndex l : ℝ) := by
  unfold qVFamPaperRootCoefficient rootStackIndex
  push_cast
  have hq : (0 : ℝ) < ((qVFamily T b).order : ℝ) := by
    exact_mod_cast (qVFamily T b).order_pos
  have hd : (0 : ℝ) < (2 * (l.value : ℝ)) := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    nlinarith
  rw [Real.log_div hq.ne' hd.ne']
  ring

/-- The signed q-coefficient log is bounded by the signed least-hull log,
with the gap exactly the log of the Jones index. -/
theorem qCoefficientLog_le_leastHullCoefficientLog :
    -Real.log ((qVFamily T b).order : ℝ) ≤
      -Real.log (qVFamPaperRootCoefficient T b) := by
  rw [leastHullCoefficientLog_eq_qCoefficientLog_add_log_index]
  have hidx : 0 ≤ Real.log (rootStackIndex l : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ rootStackIndex l by
      have := rootStackIndex_ge_two l
      omega)
  linarith

/-- **Exact no-go/criterion.**  The literal identification of the least-hull
coefficient with the Jones normalization 1/(2l) holds exactly when the q
order is 1. -/
theorem leastHullCoefficient_eq_jonesNormalization_iff :
    qVFamPaperRootCoefficient T b = jonesNormalization l ↔
      (qVFamily T b).order = 1 := by
  unfold qVFamPaperRootCoefficient jonesNormalization jonesIndex rootStackIndex
  push_cast
  have hden : (2 * (l.value : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  constructor
  · intro h
    have h' : ((qVFamily T b).order : ℝ) * (2 * (l.value : ℝ)) =
        (1 : ℝ) * (2 * (l.value : ℝ)) :=
      (div_eq_div_iff hden hden).mp h
    have h'' : ((qVFamily T b).order : ℝ) = 1 := by
      simpa using mul_right_cancel₀ hden h'
    exact_mod_cast h''
  · intro h
    rw [h]
    norm_num

/-- If the q order is not 1, the least-hull coefficient is not the bare Jones
normalization. -/
theorem leastHullCoefficient_ne_jonesNormalization_of_order_ne_one
    (h : (qVFamily T b).order ≠ 1) :
    qVFamPaperRootCoefficient T b ≠ jonesNormalization l := by
  intro heq
  exact h ((leastHullCoefficient_eq_jonesNormalization_iff (l := l) T b).mp heq)

/-- For q order > 1 the least-hull coefficient is strictly larger than the
bare Jones normalization. -/
theorem jonesNormalization_lt_leastHullCoefficient_of_one_lt_order
    (h : 1 < (qVFamily T b).order) :
    jonesNormalization l < qVFamPaperRootCoefficient T b := by
  unfold jonesNormalization qVFamPaperRootCoefficient jonesIndex rootStackIndex
  push_cast
  have hden : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    nlinarith
  rw [div_lt_div_iff_of_pos_right hden]
  exact_mod_cast h

/-! ## 6. The paper coefficient log-volumes and the index factor -/

section LogVolume

variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The paper q coefficient log-volume at b: -order(q) log p. -/
noncomputable def paperQCoefficientLogVolume : ℝ :=
  -((qVFamily T b).order : ℝ) * Real.log (qVFamTensorP T b : ℝ)

/-- The least lambda-O hull coefficient log-volume at the paper root
coefficient: -(order(q)/(2l)) log p. -/
noncomputable def paperLeastHullCoefficientLogVolume : ℝ :=
  -((qVFamPaperRootCoefficient T b) * Real.log (qVFamTensorP T b : ℝ))

theorem paperLeastHullCoefficientLogVolume_eq_normalizedTrace_qLogVolume :
    paperLeastHullCoefficientLogVolume T b =
      (1 / (rootStackIndex l : ℝ)) * paperQCoefficientLogVolume T b := by
  unfold paperLeastHullCoefficientLogVolume paperQCoefficientLogVolume
    qVFamPaperRootCoefficient rootStackIndex
  push_cast
  ring

/-- The paper coefficient log-volume comparison: the q side is bounded by the
least-hull side, and the factor is exactly the Jones normalization
1/(2l). -/
theorem paperQLogVolume_le_paperLeastHullLogVolume :
    paperQCoefficientLogVolume T b ≤ paperLeastHullCoefficientLogVolume T b := by
  rw [paperLeastHullCoefficientLogVolume_eq_normalizedTrace_qLogVolume]
  have hq : paperQCoefficientLogVolume T b ≤ 0 := by
    unfold paperQCoefficientLogVolume
    have horder : (0 : ℝ) ≤ ((qVFamily T b).order : ℝ) := by positivity
    have hp : (1 : ℝ) < (qVFamTensorP T b : ℝ) := by
      exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
    have hlog : 0 ≤ Real.log (qVFamTensorP T b : ℝ) := Real.log_nonneg hp.le
    nlinarith
  have hκ_nonneg : 0 ≤ 1 / (rootStackIndex l : ℝ) := by positivity
  have hκ_le_one : 1 / (rootStackIndex l : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast rootStackIndex_pos l)]
    exact_mod_cast (show 1 ≤ rootStackIndex l by
      have := rootStackIndex_ge_two l
      omega)
  have h := mul_le_mul_of_nonpos_left hκ_le_one hq
  nlinarith

end LogVolume

end Comparison

end LeanFormal.IUT.XiFPaper.W3RootStackTraceIndexActual

end
