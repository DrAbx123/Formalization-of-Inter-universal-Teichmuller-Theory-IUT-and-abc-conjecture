/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A845 hull: C-route §12.1 L1–L5 local volume assembly

L1 shell volume: `log mu_paper = (1+[p=2]-1/e-r/n) log p` (`logMuPaper`).
L2 shell exponent: tame `h_w = 1 - 1/e` (`unitLogLattice_*` green partial).
L3 tensor packet: `hullPacket = Σ_c w_c Σ_j rho_cj log p` (`Mzk1HullPacketFormulaActual`).
L4 procession averages: paper states `avg(j+1) = (l+5)/4`, `avg(j²) = l(l+1)/12`.
L5 assembled volume: `V = ((l+5)/4) * D_exact`.

Here L1/L2/L3/L5 shapes are defined; L4 is recorded as input because the
exact procession weight normalization is not formalized in repo.  Numerical
consistency checks are proved where possible. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalVolumeAssemblyActual

/-- L1: paper shell log-volume. -/
def logMuPaper (p e r n : ℝ) : ℝ :=
  (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p

theorem logMuPaper_eq (p e r n : ℝ) :
    logMuPaper p e r n =
      (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p := rfl

/-- L2: tame shell exponent `1 - 1/e`. -/
def tameShellExponent (e : ℝ) : ℝ := 1 - 1 / e

theorem tameShellExponent_eq (e : ℝ) : tameShellExponent e = 1 - 1 / e := rfl

/-- L2: positivity of the tame exponent for `e >= 1`. -/
theorem tameShellExponent_nonneg (e : ℝ) (he : 1 ≤ e) : 0 ≤ tameShellExponent e := by
  unfold tameShellExponent
  have hepos : 0 < e := lt_of_lt_of_le zero_lt_one he
  have h : 1 / e ≤ 1 := by
    rw [div_le_one hepos]
    exact he
  linarith

/-- L3: hull packet formula (finite/tame form). -/
def hullPacketShape {ι : Type*} [Fintype ι] (w rho : ι → ℝ) (logp : ℝ) : ℝ :=
  ∑ i, w i * rho i * logp

theorem hullPacketShape_eq {ι : Type*} [Fintype ι] (w rho : ι → ℝ) (logp : ℝ) :
    hullPacketShape w rho logp = ∑ i, w i * rho i * logp := rfl

/-- L4: paper procession averages (input, not proved). -/
def avgJPlusOneShape (l : ℝ) : ℝ := (l + 5) / 4

def avgJSquareShape (l : ℝ) : ℝ := l * (l + 1) / 12

theorem avgJSquareShape_def (l : ℝ) : avgJSquareShape l = l * (l + 1) / 12 := rfl

/-- L5: assembled volume `V = ((l+5)/4) * D`. -/
def assembledVolume (l D : ℝ) : ℝ := ((l + 5) / 4) * D

theorem assembledVolume_eq (l D : ℝ) :
    assembledVolume l D = ((l + 5) / 4) * D := rfl

theorem assembledVolume_nonneg (l D : ℝ) (hl : 0 ≤ l) (hD : 0 ≤ D) :
    0 ≤ assembledVolume l D := by
  unfold assembledVolume
  positivity

/-- L5 conditional: if the exact volume equals the assembled shape, the shape
follows. -/
theorem volume_eq_assembled (V l D : ℝ) (h : V = assembledVolume l D) :
    V = ((l + 5) / 4) * D := by
  rw [h]; rfl

def assemblyRows : List (String × String × String) :=
  [ ("L1 shell volume", "logMuPaper = (1+[p=2]-1/e-r/n)log p", "DEF (logMuPaper); Mzk1PaperNormMuActual green"),
    ("L2 shell exponent", "tame h = 1-1/e; nonneg for e>=1", "DEF + PROVED (tameShellExponent_nonneg)"),
    ("L3 hull packet", "Σ_c w_c rho_cj log p", "DEF (hullPacketShape); Mzk1HullPacketFormulaActual green"),
    ("L4 avg(j+1)", "(l+5)/4", "INPUT (paper); not formalized"),
    ("L4 avg(j^2)", "l(l+1)/12", "INPUT (paper); shape only"),
    ("L5 assembled V", "V = ((l+5)/4)D", "DEF (assembledVolume) + conditional theorem"),
    ("L5 nonneg", "l,D>=0 => V>=0", "PROVED (assembledVolume_nonneg)"),
    ("gap", "identify actual volume with assembled shape (procession/L4 weights)", "GAP") ]

theorem assemblyRows_length : assemblyRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1LocalVolumeAssemblyActual.tameShellExponent_nonneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LocalVolumeAssemblyActual.assembledVolume_nonneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LocalVolumeAssemblyActual.volume_eq_assembled

end LeanFormal.IUT.XiFPaper.Mzk1LocalVolumeAssemblyActual

end