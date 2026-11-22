import tmp.sheaf.n8.closure.PaperC6RegionConstructed2
import tmp.sheaf.n8.closure.EtaVaryingCalibrationQOActual
import tmp.sheaf.n8.closure.EtaQRegionRepresentation

/-!
# C7 paper divisor actual 2: natural volume divisors

Actual data:
* paper C6 region/hull/Theta (PaperC6RegionConstructed2):
  h = Theta.toReal, R = regionVolume.toReal, R <= h.
* native qO Q = qORegionLogVolume X.

Natural non-endpoint construction:
  A := R (region volume), Z := h - R (hull excess), d := 1.
A,Z are actual volume quantities (Z>=0), but the model law
h - Q = Z - A is equivalent to Q = 2R.  Production gives no Q=2R theorem.
No endpoint calibration, no arbitrary divisor.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2
open scoped ENNReal

namespace LeanFormal.IUT.N8Closure.C7PaperDivisorActual2

/-- Actual paper Theta (hull log-volume). -/
noncomputable def hTheta {l : PrimeGeFive} (S : SourceInitialThetaData l)
    (P : PaperC6RegionInput S) : Real := (c6Theta S P).toReal

/-- Actual paper region log-volume. -/
noncomputable def rRegion {l : PrimeGeFive} (S : SourceInitialThetaData l)
    (P : PaperC6RegionInput S) : Real := (c6RegionVolume S P).toReal

/-- Actual qO endpoint. -/
noncomputable def Q {l : PrimeGeFive} (X : N8NativeInput l) : Real :=
  qORegionLogVolume X

/-- Actual region-volume multiplier divisor. -/
noncomputable def A {l : PrimeGeFive} (S : SourceInitialThetaData l)
    (P : PaperC6RegionInput S) : Real := rRegion S P

/-- Actual hull-excess effective zero. -/
noncomputable def Z {l : PrimeGeFive} (S : SourceInitialThetaData l)
    (P : PaperC6RegionInput S) : Real := hTheta S P - rRegion S P

theorem Z_nonneg {l : PrimeGeFive} (S : SourceInitialThetaData l)
    (P : PaperC6RegionInput S) : 0 <= Z S P := by
  unfold Z
  exact sub_nonneg.mpr (c6RegionVolume_toReal_le_theta S P)

/-- Natural model law with d=1. -/
def C7Law {l : PrimeGeFive} (X : N8NativeInput l) (S : SourceInitialThetaData l)
    (P : PaperC6RegionInput S) : Prop :=
  hTheta S P - Q X = Z S P - A S P

theorem c7Law_iff_Q_eq_two_region {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) (P : PaperC6RegionInput S) :
    C7Law X S P ↔ Q X = 2 * rRegion S P := by
  unfold C7Law A Z hTheta
  constructor <;> intro hh <;> linarith

/-- Exact missing normalization equation. -/
def MissingQOTensorNormalization {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) (P : PaperC6RegionInput S) : Prop :=
  Q X = 2 * rRegion S P

/-- Exact C7 actual divisor data, conditional on missing normalization. -/
structure C7ActualDivisors {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) (P : PaperC6RegionInput S) where
  h : Real
  Qval : Real
  Aval : Real
  Zval : Real
  kappa : Real
  Sdeg : Real
  d : Nat
  h_eq : h = hTheta S P
  Q_eq : Qval = Q X
  A_eq : Aval = A S P
  Z_eq : Zval = Z S P
  d_eq : d = 1
  kappa_eq_A : kappa = Aval
  S_eq_Z : Sdeg = Zval
  law : h - (d : Real) * Qval = Sdeg - kappa
  S_nonneg : 0 <= Sdeg

/-- Exact obstruction: no natural C7ActualDivisors without Q=2R. -/
def MissingC7ActualDivisors {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) (P : PaperC6RegionInput S) : Prop :=
  Nonempty (C7ActualDivisors X S P)

end LeanFormal.IUT.N8Closure.C7PaperDivisorActual2
