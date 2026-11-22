import tmp.sheaf.n8.closure.EtaMovingGaussianAction
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge
import Mathlib.NumberTheory.Padics.Complex

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaSourceGaussianMovement

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.N8Closure.EtaMovingGaussianAction
open scoped Padic

variable (l : PrimeGeFive)
local instance : Fact (Nat.Prime l.value) := l.factPrime

/-- The actual C3 q-unit in the algebraic closure, at the concrete theta
parameter. -/
noncomputable def etaQUnit : (PadicAlgCl l.value)ˣ :=
  (parameter l).qUnit

/-- Actual Gaussian unit `a^(j^2)` with `a = qUnit`. -/
noncomputable def sourceGaussianUnit (j : ℕ) : (PadicAlgCl l.value)ˣ :=
  (etaQUnit (l := l)) ^ (j ^ 2)

/-- Actual Gaussian scalar `a^(j^2)` in the algebraic closure. -/
noncomputable def sourceGaussianScalar (j : ℕ) : PadicAlgCl l.value :=
  ((sourceGaussianUnit (l := l) j : (PadicAlgCl l.value)ˣ) : PadicAlgCl l.value)

/-- Actual unit-sphere region in the algebraic closure. -/
def sourceUnitSphere : Set (PadicAlgCl l.value) :=
  Metric.sphere (0 : PadicAlgCl l.value) 1

/-- Actual Gaussian multiplication action on the source unit sphere. -/
def sourceGaussianAction (j : ℕ) : Set (PadicAlgCl l.value) :=
  (fun x : PadicAlgCl l.value => sourceGaussianScalar (l := l) j * x) ''
    sourceUnitSphere (l := l)

/-- The actual qUnit norm is strictly less than one: it is the image of the
Tate q-parameter under the isometric embedding into the algebraic closure. -/
theorem etaQUnit_norm_lt_one :
    ‖((etaQUnit l : (PadicAlgCl l.value)ˣ) : PadicAlgCl l.value)‖ < 1 := by
  have hval : ((etaQUnit l : (PadicAlgCl l.value)ˣ) : PadicAlgCl l.value) =
      (((parameter l).q : ℚ_[l.value]) : PadicAlgCl l.value) := by
    simp [etaQUnit, ConcreteTateParameter.qUnit]
  rw [hval, PadicAlgCl.norm_extends]
  exact (parameter l).q_norm_lt_one

theorem sourceGaussianScalar_norm_lt_one (j : ℕ) (hj : j ≠ 0) :
    ‖sourceGaussianScalar l j‖ < 1 := by
  have hbase_nonneg : 0 ≤ ‖((etaQUnit l : (PadicAlgCl l.value)ˣ) :
      PadicAlgCl l.value)‖ := norm_nonneg _
  have hbase_lt := etaQUnit_norm_lt_one (l := l)
  have hpow_lt : ‖((etaQUnit l : (PadicAlgCl l.value)ˣ) : PadicAlgCl l.value)‖ ^
      (j ^ 2) < 1 :=
    pow_lt_one₀ hbase_nonneg hbase_lt (pow_ne_zero 2 hj)
  rw [sourceGaussianScalar, sourceGaussianUnit, Units.val_pow_eq_pow_val, norm_pow]
  exact hpow_lt

theorem sourceGaussianScalar_norm_ne_one (j : ℕ) (hj : j ≠ 0) :
    ‖sourceGaussianScalar l j‖ ≠ 1 :=
  ne_of_lt (sourceGaussianScalar_norm_lt_one (l := l) j hj)

/-- Actual movement: `a^(j^2)` with `a = C3.qUnit` moves the actual unit
sphere in the algebraic closure. -/
theorem sourceGaussianAction_ne_unitSphere (j : ℕ) (hj : j ≠ 0) :
    sourceGaussianAction (l := l) j ≠ sourceUnitSphere l := by
  exact scaling_image_sphere_ne_of_norm_ne_one (sourceGaussianScalar l j)
    (sourceGaussianScalar_norm_ne_one (l := l) j hj)

/-! ## Exact source condition -/

/-- Exact source hypothesis for any Gaussian unit `a`: movement of the unit
sphere under `a^(j^2)` needs the actual norm of `a` to be different from one. -/
def SourceGaussianUnitMovesSphere (a : (PadicAlgCl l.value)ˣ) : Prop :=
  ‖((a : (PadicAlgCl l.value)ˣ) : PadicAlgCl l.value)‖ ≠ 1

theorem sourceGaussianUnitMovesSphere_of_qUnit :
    SourceGaussianUnitMovesSphere (l := l) (etaQUnit l) :=
  ne_of_lt (etaQUnit_norm_lt_one l)

end LeanFormal.IUT.N8Closure.EtaSourceGaussianMovement
