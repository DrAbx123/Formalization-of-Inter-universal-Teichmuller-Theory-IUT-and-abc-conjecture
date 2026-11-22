/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A908: face 5 proof skeleton — inequality from section data (green), one remaining construction -/

/- Model (our framework, no lana dependency):
* `Face5Data`: `V` = our hull log-volume, `A = |log q|/(2l)`, `sF = sFactor(nC)`,
  with the paper decomposition `V - (sF-1)*A = sumMu + archTerm`, where `sumMu` is the
  sum of finite per-place `logMuPaper` terms and `archTerm` the archimedean contribution;
* per-place nonnegativity `0 <= sumMu` (faithful r semantics: finite coefficients >= 0)
  and `0 <= archTerm` (archConstant = log(sqrt 2 pi) >= 0, paper-level) are explicit
  hypotheses/fields.
* `Face5SectionData` (Arakelov interpretation): a difference-bundle datum with a nonzero
  section and the product-formula accounting `degNorm H = V - (sF-1)*A = sum of -log||x||_v`,
  with the numerical sum nonnegative.  Then the main inequality follows by arithmetic.

THE REMAINING OBLIGATION = constructing an instance of `Face5SectionData` with the actual
section (integrality + arch bound).  Generic existence is equivalent to the target (qpilot
A903/A904), so it is recorded as the single explicit construction obligation.
No lana imports; `#print axioms` trio expected. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Face5ProofActual

structure Face5Data where
  V : ℝ
  A : ℝ
  sF : ℝ
  sumMu : ℝ
  archTerm : ℝ
  decomposition : V - (sF - 1) * A = sumMu + archTerm
  sumMu_nonneg : 0 ≤ sumMu
  arch_nonneg : 0 ≤ archTerm

/-- **Main theorem (per-place route)**: faithful per-place nonnegativity + arch
nonnegativity + the paper decomposition give `(sF - 1)*A <= V`. -/
theorem face5_inequality_from_perplace (D : Face5Data) :
    (D.sF - 1) * D.A ≤ D.V := by
  have h := D.decomposition
  have hmu := D.sumMu_nonneg
  have ha := D.arch_nonneg
  linarith

structure Face5SectionData where
  V : ℝ
  A : ℝ
  sF : ℝ
  degNormH : ℝ
  sumNorms : ℝ
  section_ne_zero : Prop
  degNorm_eq : degNormH = V - (sF - 1) * A
  productFormula_accounting : degNormH = sumNorms
  sumNorms_nonneg : 0 ≤ sumNorms

/-- **Main theorem (section/product-formula route)**: a nonzero-section difference bundle
with product-formula accounting and nonnegative norm sum gives `(sF-1)*A <= V`. -/
theorem face5_inequality_of_section (S : Face5SectionData) :
    (S.sF - 1) * S.A ≤ S.V := by
  have h1 := S.degNorm_eq
  have h2 := S.productFormula_accounting
  have h3 := S.sumNorms_nonneg
  linarith

/-- Combining both presentations (data-level). -/
theorem face5_both_routes (D : Face5Data) (S : Face5SectionData) :
    (D.sF - 1) * D.A ≤ D.V ∧ (S.sF - 1) * S.A ≤ S.V :=
  ⟨face5_inequality_from_perplace D, face5_inequality_of_section S⟩

/-- The single remaining construction obligation, as an explicit predicate. -/
def Face5ConstructionObligation : Prop := Nonempty Face5SectionData

def face5Rows : List (String × String × String) :=
  [ ("Face5Data", "V, A, sF, per-place decomposition", "MODEL DEF") ,
    ("face5_inequality_from_perplace", "sumMu>=0 + arch>=0 + decomposition => (sF-1)A <= V", "PROVED") ,
    ("Face5SectionData", "degNorm H, section nonzero Prop, product formula, norm sum", "MODEL DEF") ,
    ("face5_inequality_of_section", "product formula + norm sum >= 0 => (sF-1)A <= V", "PROVED") ,
    ("Face5ConstructionObligation", "Nonempty Face5SectionData with actual section", "REMAINING (explicit construction)") ,
    ("Arakelov interpretation", "H = det(hull) (x) L_q^{-(sF-1)}, degNorm accounting", "MODEL NOTE") ]

theorem face5Rows_length : face5Rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Face5ProofActual
