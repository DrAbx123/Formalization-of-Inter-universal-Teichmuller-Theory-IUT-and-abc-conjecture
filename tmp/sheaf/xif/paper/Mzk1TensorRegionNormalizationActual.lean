/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import Mathlib.Tactic

/-! # A1124: tensor region normalization and R/M bounds

| field | value |
|---|---|---|
| Status | PARTIAL/CONDITIONAL: `tensorIntegralRegion_mono`, `tensorIntegerRegionL`, `tensorIntegerRegionL_subset_actual`, `haar_actual_ge_one` are proved; `R_nonpos`/`M_nonneg` take the finiteness of the actual region as an **explicit theorem hypothesis** `hfin` (not a field of the shared structure). |
| Source | `Mzk1C3LogShellTensorLActual:70/80/100`; `LogarithmLocalInverse:120` (`integers_subset_integralLogShell`); `FinitePadicTensorIntegralRegion:20` (`tensorIntegralRegion`) |
| Semantic | No field was added to `NormalizedTensorHaarData`; `hfin : mu (actualRegion) < ⊤` is an explicit hypothesis of `R_nonpos`/`M_nonneg`. The raw finiteness is still an unproved GAP. |
| GAP | positivity/finiteness of `mu (tensorIntegerRegionL)` (nonempty interior/compact tensor image) is not proved; the normalized measure is not identified with the raw S2807 `Measure.addHaar` (they differ by the scalar `mu(tensor O)`). |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1TensorRegionNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

section TensorMono

universe u

variable {ι : Type*} [Fintype ι]
variable {p : ℕ} [Fact p.Prime]
variable {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)]
  [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]

/-- The tensor integral region is monotone in the product region. -/
theorem tensorIntegralRegion_mono
    {S T : (i : ι) → Set (M i)} (h : ∀ i, S i ⊆ T i) :
    tensorIntegralRegion (p := p) M S ⊆ tensorIntegralRegion (p := p) M T := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, fun i _ => h i (hx i (Set.mem_univ i)), rfl⟩

end TensorMono

section C3

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable (C3L : SourcePilotRegionDataL (I := I))

local instance tensorRegionMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlockL (I := I) C3L) := borel _

local instance tensorRegionBorelSpace :
    BorelSpace (C3LogShellTensorBlockL (I := I) C3L) := ⟨rfl⟩

/-- The tensor image of the product of local integer rings. -/
noncomputable def tensorIntegerRegionL :
    Set (C3LogShellTensorBlockL (I := I) C3L) :=
  letI : Fact C3L.p.Prime := C3L.hp
  tensorIntegralRegion (p := C3L.p)
    (M := fun i => C3LogShellFiberL (I := I) C3L i)
    (fun i => (Integers (C3LogShellFiberL (I := I) C3L i) : Set _))

/-- The integer tensor region lies in the actual log-shell tensor region. -/
theorem tensorIntegerRegionL_subset_actual :
    tensorIntegerRegionL (I := I) C3L ⊆ actualC3LogShellTensorRegionL (I := I) C3L := by
  letI : Fact C3L.p.Prime := C3L.hp
  apply tensorIntegralRegion_mono
  intro i
  rw [actualC3LogShellL_eq_integralLogShell]
  exact integers_subset_integralLogShell

/-- Explicit normalization data: a positive additive Haar measure with
`mu (tensorIntegerRegionL) = 1`.  The existence of such a normalized measure
(positivity/finiteness of the raw mass) is the exact GAP, carried as data. -/
structure NormalizedTensorHaarData where
  mu : Measure (C3LogShellTensorBlockL (I := I) C3L)
  isAddHaar : Measure.IsAddHaarMeasure mu
  mass_integer_region : mu (tensorIntegerRegionL (I := I) C3L) = 1

/-- Under the normalization, the actual region has Haar mass at least one. -/
theorem haar_actual_ge_one (D : NormalizedTensorHaarData (I := I) C3L) :
    (1 : ENNReal) ≤ D.mu (actualC3LogShellTensorRegionL (I := I) C3L) := by
  rw [← D.mass_integer_region]
  exact measure_mono (tensorIntegerRegionL_subset_actual (I := I) C3L)

/-- The normalized target `R = -log mu(actual region)`. -/
noncomputable def RTarget (D : NormalizedTensorHaarData (I := I) C3L) : ℝ :=
  - Real.log (D.mu (actualC3LogShellTensorRegionL (I := I) C3L)).toReal

/-- The normalized `R` is non-positive. -/
theorem R_nonpos (D : NormalizedTensorHaarData (I := I) C3L)
    (hfin : D.mu (actualC3LogShellTensorRegionL (I := I) C3L) < ⊤) :
    RTarget (I := I) C3L D ≤ 0 := by
  unfold RTarget
  have h1 : (1 : ENNReal) ≤ D.mu (actualC3LogShellTensorRegionL (I := I) C3L) :=
    haar_actual_ge_one (I := I) C3L D
  have h1' : (1 : ℝ) ≤ (D.mu (actualC3LogShellTensorRegionL (I := I) C3L)).toReal := by
    have hb : D.mu (actualC3LogShellTensorRegionL (I := I) C3L) ≠ ⊤ := hfin.ne
    simpa using ENNReal.toReal_mono hb h1
  have hlog : 0 ≤ Real.log (D.mu (actualC3LogShellTensorRegionL (I := I) C3L)).toReal :=
    Real.log_nonneg h1'
  linarith

/-- Consequently `M = A - R` is non-negative for `A >= 0`. -/
theorem M_nonneg (D : NormalizedTensorHaarData (I := I) C3L)
    (hfin : D.mu (actualC3LogShellTensorRegionL (I := I) C3L) < ⊤) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ A - RTarget (I := I) C3L D := by
  have hR : RTarget (I := I) C3L D ≤ 0 := R_nonpos (I := I) C3L D hfin
  linarith

def rows : List (String × String × String) :=
  [ ("tensorIntegralRegion_mono", "product/image monotonicity", "PROVED"),
    ("tensorIntegerRegionL", "tensorIntegralRegion (prod Integers)", "DEF"),
    ("tensorIntegerRegionL_subset_actual", "O-region subset actual region", "PROVED"),
    ("NormalizedTensorHaarData", "mu/addHaar/mass=1", "DEF + GAP (exists)"),
    ("haar_actual_ge_one", "mass actual >= 1", "PROVED conditional"),
    ("R_nonpos", "R <= 0 given explicit hfin", "PROVED conditional"),
    ("M_nonneg", "A - R >= 0 for A>=0 given explicit hfin", "PROVED conditional") ]

theorem rows_length : rows.length = 7 := rfl

end C3

end LeanFormal.IUT.XiFPaper.Mzk1TensorRegionNormalizationActual

end