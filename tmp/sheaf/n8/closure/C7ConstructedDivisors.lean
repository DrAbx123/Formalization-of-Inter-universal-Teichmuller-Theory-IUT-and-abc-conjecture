import tmp.sheaf.n8.closure.O4ActualTensorHullTarget
import tmp.sheaf.n8.closure.EtaIntegersZpModuleActual
import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.EtaVaryingCalibrationQOActual

/-!
# C7 constructed divisors

Actual C7 data from actual tensor/edge objects:
* Q = qORegionLogVolume (actual qO endpoint)
* h = hTensor 1 (actual finite tensor hull log-volume)
* A = log of the actual tensor edge lattice index
* d = 1 (one-factor block), Z = 0 (empty effective zero), S = 0, kappa = A.

The natural actual divisors do not satisfy `h - d Q = S - kappa`; the exact
missing comparison/effective-zero source data is recorded.  No arbitrary
divisor is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7ConstructedDivisors

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.O4ActualTensorHullTarget
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct BigOperators

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev Zp : Type := ℤ_[nativePrime X]
abbrev g0 : Kf X := gNonIntegral X

local instance : Module (Zp X) (Kf X) :=
  Module.compHom (Kf X) (algebraMap (Zp X) (ℚ_[nativePrime X]))
local instance : Module (Zp X) (E X) :=
  Module.compHom (E X) (algebraMap (Zp X) (ℚ_[nativePrime X]))
local instance : MeasurableSpace (E X) :=
  MeasurableSpace.map (tau X).symm (inferInstance : MeasurableSpace (Kf X))

/-- Actual tensor edge lattice index. -/
noncomputable def c7LatticeIndex (X : N8NativeInput l) : ℕ :=
  Nat.card (LvSub X (g0 X) ⧸
    (Submodule.map (edgeZp X (g0 X) (gNonIntegral_ne_zero X)) (LuSub X)).comap
      (LvSub X (g0 X)).subtype)

noncomputable def c7A (X : N8NativeInput l) : ℝ := Real.log (c7LatticeIndex X)
noncomputable def c7Q (X : N8NativeInput l) : ℝ := qORegionLogVolume X
noncomputable def c7H (X : N8NativeInput l) : ℝ := hTensor X 1

theorem c7H_pos : 0 < c7H X := by
  unfold c7H
  rw [hTensor_eq]
  have hp1 : (1 : ℝ) < (nativePrime X : ℝ) :=
    by exact_mod_cast (Fact.out : Nat.Prime (nativePrime X)).one_lt
  have hg : ‖g0 X‖ = (nativePrime X : ℝ) := by
    change ‖(fPlaceP X)⁻¹‖ = (nativePrime X : ℝ)
    rw [norm_inv, fPlaceP_norm, inv_inv]
  have hlog : 0 < Real.log ‖g0 X‖ := by
    rw [hg]
    exact Real.log_pos hp1
  have hdpos : (0 : ℝ) <
      (Module.finrank ℚ_[nativePrime X] (Kf X) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  norm_num
  exact mul_pos hdpos hlog

theorem c7Q_neg : c7Q X < 0 := by
  unfold c7Q
  rw [EtaVaryingCalibrationQOActual.qORegionLogVolume_eq_qPilotSignedLog X]
  exact qPilotSignedLog_neg X

theorem c7A_nonneg : 0 ≤ c7A X := by
  unfold c7A
  exact Real.log_natCast_nonneg _

/-- Natural actual divisors: d=1, empty effective zero Z=0, S=0, kappa=A. -/
structure C7ActualDivisors (X : N8NativeInput l) where
  h : ℝ
  Q : ℝ
  A : ℝ
  Z : ℝ
  kappa : ℝ
  S : ℝ
  d : ℕ
  h_eq : h = c7H X
  Q_eq : Q = c7Q X
  A_eq : A = c7A X
  Z_eq : Z = 0
  kappa_eq : kappa = A
  S_eq : S = Z

noncomputable def c7Divisors : C7ActualDivisors X where
  h := c7H X
  Q := c7Q X
  A := c7A X
  Z := 0
  kappa := c7A X
  S := 0
  d := 1
  h_eq := rfl
  Q_eq := rfl
  A_eq := rfl
  Z_eq := rfl
  kappa_eq := rfl
  S_eq := rfl

theorem c7_law_fails :
    ¬ (c7Divisors X).h - ((c7Divisors X).d : ℝ) * (c7Divisors X).Q =
      (c7Divisors X).S - (c7Divisors X).kappa := by
  intro h
  have hval : c7H X - c7Q X = -c7A X := by
    simpa [c7Divisors] using h
  have hpos : 0 < c7H X - c7Q X := by
    have := c7H_pos X
    have := c7Q_neg X
    linarith
  have hle : -c7A X ≤ 0 := neg_nonpos.mpr (c7A_nonneg X)
  linarith

/-- Exact missing C7 source comparison: actual effective-zero/comparison data
with `h - d Q = S - kappa`. -/
def MissingC7ComparisonMorphism (X : N8NativeInput l) : Prop :=
  ∃ (C : C7ActualDivisors X), C.h - (C.d : ℝ) * C.Q = C.S - C.kappa

end LeanFormal.IUT.N8Closure.C7ConstructedDivisors