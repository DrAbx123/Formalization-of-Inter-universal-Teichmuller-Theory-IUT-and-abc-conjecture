/-
# S824: actual stacky Haar log-volume on the finite root stack L(mu_2l)

Task W1 (orbifold/stacky upgrade).  The earlier Task F memo accepted the
orbifold/action-groupoid route only for the statement "1/(2l) normalization"
at the level of an abstract fundamental-domain measure identity.  This file
builds the actual measure-theoretic layer on the finite root stack of
`S782FiniteRootStackExtensionActual`:

* the primitive 2l-th root of unity `stackMuUnit` is a unit of finite order,
  hence its distributive Haar character is 1;
* consequently the inherited additive Haar `rootStackHaar` is invariant under
  the mu_2l action `u |-> stackMuUnit * u` (the quotient-measure prerequisite);
* for the actual root section `stackRootUnit` and q section `stackQUnit` of
  S782 (root^(2l) = q), the *actual* Haar log-volumes satisfy
  `log V(root ball) = (1/(2l)) * log V(q ball)`; this is the q[2u]
  normalization as an actual measure theorem, not a convention;
* the log-volume of the root ball is independent of the chosen 2l-th root
  (branch independence of the paper Theta value "up to mu_2l").

The last section relates the stacky log to the S793/S799 paper least
lambda*O hull log.  The actual root unit has norm p^(-c_norm/(2l)) with
`c_norm = qVFamNormalizedCoefficient` (S709), while the paper least hull is
built at coefficient `order/(2l)` with `order = qVFamily.order`.  Under the
explicit character/norm comparison `StackCharacterNormComparison n` (the
Haar determinant of multiplication by u is the n-th power of the spectral
norm; the only input not available in the current tree), the degree-normalized
stacky log equals `-c_norm/(2l) * log p`.  Hence the identification with the
paper least-hull log `-order/(2l) * log p` is *equivalent* to
`c_norm = order` (the S736 norm-instance gap), not an unconditional identity.
This is an explicit no-go/dichotomy, not a surrogate: no target is changed,
no completion root is invented, and the least hull remains the S793 set.

No sorry, no axiom, no fake carrier.
-/
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

noncomputable section
open scoped BigOperators NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The mu_2l action and Haar invariance -/

/-- The primitive 2l-th root of unity as an element of the finite root stack. -/
noncomputable def stackMuElem : rootStackExtension T b :=
  ((stackMuUnit (l := l) T b : (rootStackExtension T b)ˣ) : rootStackExtension T b)

theorem stackMuElem_pow :
    stackMuElem (l := l) T b ^ (2 * l.value) = 1 := by
  unfold stackMuElem stackMuUnit
  rw [Units.val_mk0]
  apply Subtype.ext
  change (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
    rootNormedAmbient T b) ^ (2 * l.value)) = 1
  exact stackMuRoot_pow T b

theorem stackMuUnit_pow_twoL :
    stackMuUnit (l := l) T b ^ (2 * l.value) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact stackMuElem_pow (l := l) T b

/-- A positive real with a positive power equal to one is one. -/
theorem nnreal_pow_eq_one {x : NNReal} {n : Nat} (hn : 0 < n) (h : x ^ n = 1) : x = 1 := by
  have hx : (0 : Real) <= (x : Real) := x.coe_nonneg
  have h' : (x : Real) ^ n = (1 : Real) ^ n := by
    rw [one_pow]
    exact_mod_cast h
  exact NNReal.coe_injective ((pow_left_inj₀ hx zero_le_one hn.ne').mp h')

/-- The distributive Haar character of a finite-order unit is one. -/
theorem distribHaarChar_finiteOrder_eq_one {n : Nat} (hn : 0 < n)
    (u : (rootStackExtension T b)ˣ) (h : u ^ n = 1) :
    MeasureTheory.distribHaarChar (rootStackExtension T b) u = 1 := by
  apply nnreal_pow_eq_one hn
  rw [← map_pow, h, map_one]

/-- The mu_2l-generator `stackMuUnit` has trivial Haar character. -/
theorem distribHaarChar_stackMuUnit_eq_one :
    MeasureTheory.distribHaarChar (rootStackExtension T b)
      (stackMuUnit (l := l) T b) = 1 :=
  distribHaarChar_finiteOrder_eq_one (l := l) T b
    (Nat.mul_pos (by norm_num) l.prime.pos) _
    (stackMuUnit_pow_twoL (l := l) T b)

/-- The inherited Haar measure on the finite root stack is invariant under the
mu_2l action: the quotient/stacky measure is well defined. -/
theorem rootStackHaar_smul_stackMuUnit (S : Set (rootStackExtension T b)) :
    rootStackHaar (l := l) T b (stackMuUnit (l := l) T b • S) =
      rootStackHaar (l := l) T b S := by
  haveI hhaar : (rootStackHaar (l := l) T b).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)
  haveI hreg : (rootStackHaar (l := l) T b).Regular :=
    Measure.regular_addHaarMeasure (K₀ := Classical.arbitrary _)
  have h := MeasureTheory.distribHaarChar_mul (A := rootStackExtension T b)
    (G := (rootStackExtension T b)ˣ) (μ := rootStackHaar (l := l) T b)
    (g := stackMuUnit (l := l) T b) (s := S)
  rw [distribHaarChar_stackMuUnit_eq_one] at h
  simpa using h.symm

/-! ## 2. The stacky log-volume of a dilated unit ball -/

/-- The unit ball of the finite root stack (the integral structure). -/
noncomputable def stackUnitBall : Set (rootStackExtension T b) :=
  Metric.closedBall (0 : rootStackExtension T b) 1

/-- Log-volume relative to the unit ball; this is the unweighted local
log-volume used by the paper on the root line. -/
noncomputable def stackyLogVolume (μ : Measure (rootStackExtension T b))
    (S : Set (rootStackExtension T b)) : Real :=
  Real.log (μ S).toReal - Real.log (μ (stackUnitBall T b)).toReal

theorem stackyLogVolume_unitBall (μ : Measure (rootStackExtension T b)) :
    stackyLogVolume (l := l) T b μ (stackUnitBall (l := l) T b) = 0 := by
  unfold stackyLogVolume
  ring

theorem unitBall_pos (μ : Measure (rootStackExtension T b)) [μ.IsAddHaarMeasure] :
    0 < μ (stackUnitBall (l := l) T b) := by
  apply Measure.measure_pos_of_nonempty_interior (μ := μ)
  exact ⟨0, Metric.ball_subset_interior_closedBall
    (Metric.mem_ball_self (by norm_num : (0:Real) < 1))⟩

theorem unitBall_fin (μ : Measure (rootStackExtension T b)) [μ.IsAddHaarMeasure] :
    μ (stackUnitBall (l := l) T b) < ⊤ :=
  (isCompact_closedBall (0 : rootStackExtension T b) 1).measure_lt_top

/-- Multiplication by a unit is an isometry of the additive group, so the
dilated unit ball is exactly the ball of radius `||u||`. -/
theorem closedBall_smul_unit_eq (u : (rootStackExtension T b)ˣ) :
    u • stackUnitBall (l := l) T b =
      Metric.closedBall (0 : rootStackExtension T b) ‖(u : rootStackExtension T b)‖ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [stackUnitBall, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    rw [smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro hx
    refine ⟨((u⁻¹ : (rootStackExtension T b)ˣ) : rootStackExtension T b) * x, ?_, ?_⟩
    · simp only [stackUnitBall, Metric.mem_closedBall, dist_zero_right]
      change ‖((u⁻¹ : (rootStackExtension T b)ˣ) : rootStackExtension T b) * x‖ ≤ 1
      rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv]
      have hu : 0 < ‖(u : rootStackExtension T b)‖ :=
        norm_pos_iff.mpr (Units.ne_zero u)
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      rw [inv_mul_le_iff₀ hu]
      simpa using hx
    · change ((u : rootStackExtension T b)) * (((u⁻¹ : (rootStackExtension T b)ˣ) :
        rootStackExtension T b) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

/-- The log-volume of the dilated unit ball is the log of the distributive
Haar character (the p-adic determinant of the multiplier). -/
theorem stackyLogVolume_closedBall_unit (μ : Measure (rootStackExtension T b))
    [μ.IsAddHaarMeasure] [μ.Regular] (u : (rootStackExtension T b)ˣ) :
    stackyLogVolume (l := l) T b μ
        (Metric.closedBall (0 : rootStackExtension T b) ‖(u : rootStackExtension T b)‖) =
      Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b) u : Real) := by
  have hpos := unitBall_pos (l := l) T b μ
  have hfin := unitBall_fin (l := l) T b μ
  have hsmul := MeasureTheory.distribHaarChar_mul (A := rootStackExtension T b)
    (G := (rootStackExtension T b)ˣ) (μ := μ) (g := u) (s := stackUnitBall (l := l) T b)
  rw [closedBall_smul_unit_eq (l := l) T b u] at hsmul
  have hpos' : μ (stackUnitBall (l := l) T b) ≠ 0 := hpos.ne'
  have hfin' : μ (stackUnitBall (l := l) T b) ≠ ⊤ := hfin.ne
  unfold stackyLogVolume
  rw [← hsmul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hdet : (MeasureTheory.distribHaarChar (rootStackExtension T b) u : Real) ≠ 0 := by
    exact_mod_cast (MeasureTheory.distribHaarChar_pos (A := rootStackExtension T b)
      (g := u)).ne'
  have hm : (μ (stackUnitBall (l := l) T b)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos' hfin').ne'
  rw [Real.log_mul hdet hm]
  ring

/-! ## 3. Root section, q[2u] normalization, branch independence -/

/-- The unit part of the actual root-stack section (q[2u] as an element of L). -/
noncomputable def stackRootUnit : (rootStackExtension T b)ˣ :=
  (stackRootSection (l := l) T b).1

/-- The unit part of the q section (q[1u] as an element of L). -/
noncomputable def stackQUnit : (rootStackExtension T b)ˣ :=
  (stackQSection (l := l) T b).1

theorem stackRootUnit_pow :
    stackRootUnit (l := l) T b ^ (2 * l.value) = stackQUnit (l := l) T b :=
  congrArg Prod.fst (stackRootSection_pow (l := l) T b)

/-- Root-unit log-volume equals (1/2l) times the q[1u] log-volume: the q[2u]
normalization is an actual theorem about the finite-root-stack Haar. -/
theorem stackyLogVolume_root_eq_inv_card_mul_q
    (μ : Measure (rootStackExtension T b)) [μ.IsAddHaarMeasure] [μ.Regular] :
    stackyLogVolume (l := l) T b μ
        (Metric.closedBall (0 : rootStackExtension T b) ‖(stackRootUnit (l := l) T b :
          rootStackExtension T b)‖) =
      (1 / (2 * (l.value : Real))) * stackyLogVolume (l := l) T b μ
        (Metric.closedBall (0 : rootStackExtension T b) ‖(stackQUnit (l := l) T b :
          rootStackExtension T b)‖) := by
  rw [stackyLogVolume_closedBall_unit (l := l) T b μ (stackRootUnit (l := l) T b),
    stackyLogVolume_closedBall_unit (l := l) T b μ (stackQUnit (l := l) T b)]
  have hpow : (MeasureTheory.distribHaarChar (rootStackExtension T b)
      (stackRootUnit (l := l) T b) : Real) ^ (2 * l.value) =
      (MeasureTheory.distribHaarChar (rootStackExtension T b)
        (stackQUnit (l := l) T b) : Real) := by
    have h := congrArg (fun x : NNReal => (x : Real))
      (map_pow (MeasureTheory.distribHaarChar (rootStackExtension T b))
        (stackRootUnit (l := l) T b) (2 * l.value))
    rw [stackRootUnit_pow (l := l) T b] at h
    simpa [NNReal.coe_pow] using h.symm
  have hlog := congrArg Real.log hpow
  rw [Real.log_pow] at hlog
  have hcast : ((2 * l.value : Nat) : Real) = 2 * (l.value : Real) := by push_cast; ring
  rw [hcast] at hlog
  have hn : (2 * (l.value : Real)) ≠ 0 := by
    have := l.prime.ne_zero
    positivity
  have hlog' : Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
        (stackQUnit (l := l) T b) : Real) =
      (2 * (l.value : Real)) * Real.log (MeasureTheory.distribHaarChar
        (rootStackExtension T b) (stackRootUnit (l := l) T b) : Real) := hlog.symm
  rw [hlog']
  rw [← mul_assoc]
  have h2lpos : (2 * (l.value : Real)) ≠ 0 := by
    have := l.prime.pos
    positivity
  have h2l : (1 / (2 * (l.value : Real))) * (2 * (l.value : Real)) = 1 :=
    one_div_mul_cancel h2lpos
  rw [h2l, one_mul]

/-- Branch independence: replacing the root by any root of unity multiple does
not change the log-volume of the root ball. -/
theorem stackyLogVolume_branch_independent
    (μ : Measure (rootStackExtension T b)) [μ.IsAddHaarMeasure] [μ.Regular]
    (ζ : (rootStackExtension T b)ˣ)
    (hζ : ‖(ζ : rootStackExtension T b)‖ = 1) :
    stackyLogVolume (l := l) T b μ
        (Metric.closedBall (0 : rootStackExtension T b)
          ‖(((ζ * stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ)) :
            rootStackExtension T b)‖) =
      stackyLogVolume (l := l) T b μ
        (Metric.closedBall (0 : rootStackExtension T b) ‖(stackRootUnit (l := l) T b :
          rootStackExtension T b)‖) := by
  have hnorm : ‖(((ζ * stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ)) :
      rootStackExtension T b)‖ =
      ‖(stackRootUnit (l := l) T b : rootStackExtension T b)‖ := by
    rw [Units.val_mul, norm_mul, hζ, one_mul]
  rw [hnorm]

/-! ## 4. Relation to the S793/S799 least lambda*O hull log -/

/-- The actual spectral norm of the root stack unit: p^(-c_norm/(2l)). -/
theorem stackRootUnit_norm_eq :
    ‖(stackRootUnit (l := l) T b : rootStackExtension T b)‖ =
      rootNormedElementNorm (l := l) T b := by
  unfold stackRootUnit stackRootSection stackLUnitMap rootNormedUnit rootNormedElementNorm
  rfl

theorem stackRootUnit_norm_eq_p_rpow :
    ‖(stackRootUnit (l := l) T b : rootStackExtension T b)‖ =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) := by
  rw [stackRootUnit_norm_eq (l := l) T b]
  exact rootNormedElementNorm_eq_p_rpow (l := l) T b

/-- The exact comparison input missing in the tree: the Haar determinant of
multiplication by a unit is the n-th power of the spectral norm.  For the
finite extension L/Q_p the natural n is [L : Q_p]. -/
def StackCharacterNormComparison (n : Nat) : Prop :=
  forall u : (rootStackExtension T b)ˣ,
    Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b) u : Real) =
      (n : Real) * Real.log ‖(u : rootStackExtension T b)‖

/-- Under the character/norm comparison, the degree-normalized stacky log of
the root ball is the paper coefficient formula with c_norm in place of order. -/
theorem stackyDegreeNormalizedLog_root_eq (n : Nat) (hn : 0 < n)
    (hchar : StackCharacterNormComparison (l := l) T b n) :
    (1 / (n : Real)) *
        Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
          (stackRootUnit (l := l) T b) : Real) =
      -((qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real) := by
  have hn' : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (0 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  have hrootlog : Real.log ‖(stackRootUnit (l := l) T b :
        rootStackExtension T b)‖ =
      -((qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real) := by
    rw [stackRootUnit_norm_eq_p_rpow (l := l) T b]
    change Real.log ((qVFamTensorP T b : Real) ^
      (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)))) = _
    rw [Real.log_rpow hp]
    ring
  calc
    (1 / (n : Real)) *
        Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
          (stackRootUnit (l := l) T b) : Real) =
        (1 / (n : Real)) * ((n : Real) *
          Real.log ‖(stackRootUnit (l := l) T b : rootStackExtension T b)‖) := by
      rw [hchar (stackRootUnit (l := l) T b)]
    _ = Real.log ‖(stackRootUnit (l := l) T b : rootStackExtension T b)‖ := by
      field_simp [hn']
    _ = _ := hrootlog

/-- **Dichotomy / no-go.**  Under the character/norm comparison and the
completion scaling datum at the paper coefficient, the degree-normalized
stacky log of the actual root ball equals the S799 least-hull log if and only
if c_norm = order.  The least hull itself remains the S793 set; no target is
changed. -/
theorem stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b))
    (n : Nat) (hn : 0 < n)
    (hchar : StackCharacterNormComparison (l := l) T b n) :
    (1 / (n : Real)) *
        Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
          (stackRootUnit (l := l) T b) : Real) =
      paperLeastLambdaOHullLog (l := l) T b μ ↔
      qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) := by
  rw [stackyDegreeNormalizedLog_root_eq (l := l) T b n hn hchar,
    paperLeastLambdaOHullLog_eq_formula (l := l) T b μ D]
  have hsum : (∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
    simp [paperRootCoefficientFamily, qVFamPaperRootCoefficient]
  rw [hsum]
  have hlogp : 0 < Real.log (qVFamTensorP T b : Real) :=
    Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)
  have h2l : (0 : Real) < 2 * (l.value : Real) := by
    have := l.prime.pos; positivity
  constructor
  · intro h
    have h' : (qVFamNormalizedCoefficient T b / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real) =
        (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
          Real.log (qVFamTensorP T b : Real) := by linarith
    have h'' := mul_right_cancel₀ hlogp.ne' h'
    have h2lne : (2 * (l.value : Real)) ≠ 0 := by positivity
    field_simp [h2lne] at h''
    have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
    field_simp [hl] at h''
    exact h''
  · intro h
    rw [h]
    ring

/-- Contrapositive form: if the spectral coefficient differs from the
valuation order, the stacky log and the paper least-hull log differ. -/
theorem stackyLog_ne_paperLeastHullLog_of_cnorm_ne_order
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b))
    (n : Nat) (hn : 0 < n)
    (hchar : StackCharacterNormComparison (l := l) T b n)
    (hne : qVFamNormalizedCoefficient T b ≠ ((qVFamily T b).order : Real)) :
    (1 / (n : Real)) *
        Real.log (MeasureTheory.distribHaarChar (rootStackExtension T b)
          (stackRootUnit (l := l) T b) : Real) ≠
      paperLeastLambdaOHullLog (l := l) T b μ := by
  intro h
  exact hne ((stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order (l := l) T b μ D n hn
    hchar).mp h)

/-! ## 5. Audit -/

#print axioms stackMuUnit_pow_twoL
#print axioms distribHaarChar_stackMuUnit_eq_one
#print axioms rootStackHaar_smul_stackMuUnit
#print axioms stackyLogVolume_closedBall_unit
#print axioms stackyLogVolume_root_eq_inv_card_mul_q
#print axioms stackyLogVolume_branch_independent
#print axioms stackyDegreeNormalizedLog_root_eq
#print axioms stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order

end LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual

end
