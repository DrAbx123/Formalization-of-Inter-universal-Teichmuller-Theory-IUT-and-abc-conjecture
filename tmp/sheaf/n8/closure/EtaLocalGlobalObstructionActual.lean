import tmp.sheaf.n8.closure.EtaVaryingCalibrationQOActual
import Mathlib

/-!
# Eta local/global obstruction actual

Arithmetic core of h - Q = S - kappa on the documented two-place
counterexample.  The local comparison divisors are

  alpha = (-1,0), beta = (-2,0), A = (1,0), Z = (0,0), d = 1,

so Q=-1, h=-2, kappa=1, S=0 and h-Q = S-kappa = -1, with kappa=1 != 0.  A
principal global multiplier would need degree-zero divisor, so the local
counterexample is not globally principal.

The actual qO region only supplies Q = qORegionLogVolume; no production tensor
data supplies the opposite target h or the comparison divisors A,Z.  That is
the exact data gap; no arbitrary divisor is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped BigOperators
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation

namespace LeanFormal.IUT.N8Closure.EtaLocalGlobalObstructionActual

universe u

abbrev Divisor (ι : Type u) := ι → ℝ

def degree {ι : Type u} [Fintype ι] (w : ι → ℝ) (D : Divisor ι) : ℝ :=
  ∑ i, w i * D i

structure LocalComparison (ι : Type u) [Fintype ι] (w : ι → ℝ) where
  alpha : Divisor ι
  beta : Divisor ι
  A : Divisor ι
  Z : Divisor ι
  d : ℕ
  law : ∀ i, (d : ℝ) * alpha i + Z i = beta i + A i
  Z_nonneg : ∀ i, 0 ≤ Z i

namespace LocalComparison
variable {ι : Type u} [Fintype ι] {w : ι → ℝ}

def Q (c : LocalComparison ι w) : ℝ := degree w c.alpha
def h (c : LocalComparison ι w) : ℝ := degree w c.beta
def kappa (c : LocalComparison ι w) : ℝ := degree w c.A
def S (c : LocalComparison ι w) : ℝ := degree w c.Z

end LocalComparison

def counterAlpha : Divisor (Fin 2) := fun i => if i = 0 then (-1 : ℝ) else 0
def counterBeta : Divisor (Fin 2) := fun i => if i = 0 then (-2 : ℝ) else 0
def counterA : Divisor (Fin 2) := fun i => if i = 0 then (1 : ℝ) else 0
def counterZ : Divisor (Fin 2) := fun _ => 0

def counterComparison : LocalComparison (Fin 2) (fun _ => (1 : ℝ)) where
  alpha := counterAlpha
  beta := counterBeta
  A := counterA
  Z := counterZ
  d := 1
  law := by
    intro i
    fin_cases i <;> norm_num [counterAlpha, counterBeta, counterA, counterZ]
  Z_nonneg := by intro i; simp [counterZ]

theorem counter_Q : counterComparison.Q = -1 := by
  simp [counterComparison, LocalComparison.Q, degree, counterAlpha, Fin.sum_univ_two]

theorem counter_h : counterComparison.h = -2 := by
  simp [counterComparison, LocalComparison.h, degree, counterBeta, Fin.sum_univ_two]

theorem counter_kappa : counterComparison.kappa = 1 := by
  simp [counterComparison, LocalComparison.kappa, degree, counterA, Fin.sum_univ_two]

theorem counter_S : counterComparison.S = 0 := by
  simp [counterComparison, LocalComparison.S, degree, counterZ, Fin.sum_univ_two]

/-- Concrete h-Q=S-kappa check on the documented counterexample. -/
theorem counter_identity :
    counterComparison.h - counterComparison.Q =
      counterComparison.S - counterComparison.kappa := by
  rw [counter_Q, counter_h, counter_S, counter_kappa]
  norm_num

/-- The counterexample has nonzero defect kappa=1, so it cannot come from a
global principal multiplier (which would have degree zero). -/
theorem counter_kappa_ne_zero : counterComparison.kappa ≠ 0 := by
  rw [counter_kappa]; norm_num

/-- Exact missing data: actual qO supplies Q but not the opposite tensor target
h or comparison divisors A,Z.  This is recorded as a data gap, not instantiated
by arbitrary divisors. -/
structure MissingActualComparisonTargetData (l : PrimeGeFive) (X : N8NativeInput l) where
  beta : ℝ
  A : ℝ
  Z : ℝ
  d : ℕ
  law : (d : ℝ) * qORegionLogVolume X + Z = beta + A
  Z_nonneg : 0 ≤ Z

end LeanFormal.IUT.N8Closure.EtaLocalGlobalObstructionActual
