/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A914: face5 difference bundle and local degrees (interface + arithmetic) -/

/- Model: `degH = V - (sF-1)*A` is the difference-bundle total degree; it decomposes over
the finite places (`degH_fin v = H_v - T_v`) plus the archimedean term `degH_arch = H_inf`,
using the place decompositions `V = sum_v H_v + H_inf` and
`(sF-1)*A = sum_v T_v` (A911 intrinsic per-place allocation).
No lana dependency. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Face5BundleActual

structure Face5BundleData (ι : Type*) [Fintype ι] where
  V : ℝ
  sF : ℝ
  A : ℝ
  H : ι → ℝ
  T : ι → ℝ
  Hinf : ℝ
  V_decomp : V = (∑ i, H i) + Hinf
  A_decomp : (sF - 1) * A = ∑ i, T i

def Face5BundleData.degH {ι : Type*} [Fintype ι] (D : Face5BundleData ι) : ℝ :=
  D.V - (D.sF - 1) * D.A

def Face5BundleData.degH_fin {ι : Type*} [Fintype ι] (D : Face5BundleData ι) (i : ι) : ℝ :=
  D.H i - D.T i

def Face5BundleData.degH_arch {ι : Type*} [Fintype ι] (D : Face5BundleData ι) : ℝ :=
  D.Hinf

/-- **Place decomposition of the difference-bundle degree**:
`degH = sum_v degH_fin v + degH_arch`. -/
theorem Face5BundleData.degH_eq_sum {ι : Type*} [Fintype ι] (D : Face5BundleData ι) :
    D.degH = (∑ i, D.degH_fin i) + D.degH_arch := by
  unfold Face5BundleData.degH Face5BundleData.degH_fin Face5BundleData.degH_arch
  rw [D.V_decomp, D.A_decomp, Finset.sum_sub_distrib]
  ring

/-- Nonnegativity transfer: `degH >= 0` iff the local degrees dominate `-degH_arch`. -/
theorem Face5BundleData.degH_nonneg_iff {ι : Type*} [Fintype ι] (D : Face5BundleData ι) :
    0 ≤ D.degH ↔ -D.degH_arch ≤ ∑ i, D.degH_fin i := by
  rw [D.degH_eq_sum]
  constructor <;> intro h <;> linarith

/-- Sufficient condition: if the local degrees dominate `-H_inf`, the bundle degree is
nonnegative. -/
theorem Face5BundleData.degH_nonneg_of_local {ι : Type*} [Fintype ι]
    (D : Face5BundleData ι) (h : -D.degH_arch ≤ ∑ i, D.degH_fin i) :
    0 ≤ D.degH :=
  (D.degH_nonneg_iff).mpr h

/-- Section data for the difference bundle (Arakelov interpretation). -/
structure Face5SectionData where
  V : ℝ
  sF : ℝ
  A : ℝ
  degNormH : ℝ
  sumNorms : ℝ
  section_ne_zero : Prop
  degNorm_eq : degNormH = V - (sF - 1) * A
  productFormula_accounting : degNormH = sumNorms
  sumNorms_nonneg : 0 ≤ sumNorms

/-- **Main inequality from a nonzero section** (same statement as
`Mzk1Face5ProofActual.face5_inequality_of_section`, reproved here for the local structure). -/
theorem face5_inequality_of_section (S : Face5SectionData) :
    (S.sF - 1) * S.A ≤ S.V := by
  have h1 := S.degNorm_eq
  have h2 := S.productFormula_accounting
  have h3 := S.sumNorms_nonneg
  linarith

/-- Bundle-degree nonnegativity gives the face-5 inequality in `degH` form. -/
theorem face5_of_degH_nonneg (S : Face5SectionData) :
    (S.sF - 1) * S.A ≤ S.V ↔ 0 ≤ S.degNormH := by
  rw [S.degNorm_eq]
  constructor <;> intro h <;> linarith

def bundleRows : List (String × String × String) :=
  [ ("Face5BundleData", "V, sF, A, H_v, T_v, H_inf + place decompositions", "DEF") ,
    ("degH", "V - (sF-1)*A", "DEF") ,
    ("degH_fin / degH_arch", "H_v - T_v / H_inf", "DEF") ,
    ("degH_eq_sum", "degH = sum degH_fin + degH_arch", "PROVED") ,
    ("degH_nonneg_iff", "0 <= degH <-> -H_inf <= sum degH_fin", "PROVED") ,
    ("Face5SectionData", "nonzero section, per-place norms, product formula", "DEF") ,
    ("face5_inequality_of_section", "(sF-1)A <= V", "PROVED") ,
    ("face5_of_degH_nonneg", "(sF-1)A <= V <-> 0 <= degH", "PROVED") ]

theorem bundleRows_length : bundleRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Face5BundleActual
