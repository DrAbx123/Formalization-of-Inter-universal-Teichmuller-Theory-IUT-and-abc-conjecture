/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.flt.FLT.FreyCurve.FreyPackage
import Mathlib.Tactic

/-! # A844 hull: C-route Frey shape (FLT ported tree)

FLT source (ported, commit f6c6a2f):
* `FLT/FreyCurve/FreyPackage.lean`: `FreyPackage` = `(a,b,c,p)` with
  `a^p+b^p=c^p`, pairwise coprime, `a=3 mod 4`, `b` even, `p>=5`;
  `FreyPackage.of_not_FermatLastTheoremFor_p_ge_5` (green olean).
* `FLT/FreyCurve/Basic.lean:49-68`: `freyCurveInt`/`freyCurve`;
  `FreyCurve.Δ` (:106): `Δ = (a*b*c)^(2*p) / 2^8`.

`Basic.olean` and `GaloisRep.olean` are absent in the ported build, so the
curve/Δ theorem cannot be imported here; the shape is replicated as arithmetic
and the gap recorded.  No conductor `N`, modular degree `δ`, or height relation
is defined in the FLT FreyCurve files — exact C-route gap. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1RouteCFreyShapeActual

open LeanFormal.IUT

/-- Frey discriminant shape `Δ = (a*b*c)^(2p)/2^8` (FLT `FreyCurve.Δ`). -/
def freyDeltaShape (a b c : ℤ) (p : ℕ) : ℚ := ((a * b * c : ℤ) : ℚ) ^ (2 * p) / (2 : ℚ) ^ 8

theorem freyDeltaShape_def (a b c : ℤ) (p : ℕ) :
    freyDeltaShape a b c p = ((a * b * c : ℤ) : ℚ) ^ (2 * p) / (2 : ℚ) ^ 8 := rfl

/-- Discriminant is nonzero for a Frey package (all of a,b,c nonzero). -/
theorem freyDeltaShape_ne_zero (P : FreyPackage) :
    freyDeltaShape P.a P.b P.c P.p ≠ 0 := by
  unfold freyDeltaShape
  have habc : P.a * P.b * P.c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
  have hpow : (2 * P.p) ≠ 0 := Nat.mul_ne_zero (by norm_num) P.hppos.ne'
  exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast habc)) (pow_ne_zero _ (by norm_num))

/-- FLT `FreyPackage` is green in the ported build. -/
theorem freyPackage_nonempty_of_not_FLT {p : ℕ} (pp : p.Prime) (hp5 : 5 ≤ p)
    (H : ¬ FermatLastTheoremFor p) : Nonempty FreyPackage :=
  FreyPackage.of_not_FermatLastTheoremFor_p_ge_5 pp hp5 H

/-- C-route conductor/degree shape: `N_Frey = δ² * N_odd` (the expected relation;
FLT tree has NO `N`/`δ` definition, so this is a shape only). -/
def FreyConductorDegreeShape (delta N_frey N_odd : ℕ) : Prop :=
  N_frey = delta ^ 2 * N_odd

theorem freyConductorDegreeShape_iff (delta N_frey N_odd : ℕ) :
    FreyConductorDegreeShape delta N_frey N_odd ↔
      N_frey = delta ^ 2 * N_odd := Iff.rfl

def routeCRows : List (String × String × String) :=
  [ ("FreyPackage", "FLT/FreyCurve/FreyPackage.lean structure", "GREEN olean (FreyPackage)"),
    ("FLT -> FreyPackage", "of_not_FermatLastTheoremFor_p_ge_5", "GREEN (re-exported: freyPackage_nonempty_of_not_FLT)"),
    ("Frey curve", "freyCurveInt/freyCurve (Basic.lean:49-68)", "SOURCE READ; Basic.olean absent"),
    ("discriminant", "Δ = (a*b*c)^(2p)/2^8 (Basic.lean:106)", "SOURCE READ; shape replicated (freyDeltaShape)"),
    ("Galois rep", "FLT/Deformations/RepresentationTheory/GaloisRep.lean", "SOURCE READ; olean absent"),
    ("conductor N", "not defined in FLT/FreyCurve files", "GAP"),
    ("modular degree δ", "not defined in FLT/FreyCurve files; shape N=δ²N_odd only", "GAP"),
    ("height relation", "not defined in FLT/FreyCurve files", "GAP") ]

theorem routeCRows_length : routeCRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RouteCFreyShapeActual.freyDeltaShape_ne_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RouteCFreyShapeActual.freyPackage_nonempty_of_not_FLT
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RouteCFreyShapeActual.freyConductorDegreeShape_iff

end LeanFormal.IUT.XiFPaper.Mzk1RouteCFreyShapeActual

end