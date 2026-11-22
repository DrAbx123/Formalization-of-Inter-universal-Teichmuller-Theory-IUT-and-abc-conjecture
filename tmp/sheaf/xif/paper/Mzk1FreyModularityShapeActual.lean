/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A843 hull: Frey curve / modularity shape audit

Green assets found in `LeanFormal/IUT/ABCBridge/Geometry/Frey*` (26 files):
* `FreyWeierstrassCurve.freyWeierstrassCurve`, `rationalFreyWeierstrassCurve`;
* `rationalFreyWeierstrassCurve_discriminant_natCast_sixteen_mul_sq_of_isABCTriple`:
  `Δ = 16·a²b²c²`;
* `IsABCTriple.natRadical_freyDiscriminant_eq_natRadical_product`,
  `IsABCTriple.primeFactors_freyDiscriminant_eq`;
* `frey_oddConductor_eq_oddRadical`:
  odd conductor = `∏_{p ∣ abc, p ≠ 2} p`;
* `freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP` (`q = j⁻¹`),
  `freyAbcTateCandidateQ_norm_eq_inv_freyAbcJInvariantAtP_norm`
  (`||q|| = ||j||⁻¹`), `freyTateComparisonPacket_summary`.

No green relation involving the modular parametrization degree `δ` exists.
This file records the discriminant/radical/conductor/Tate shapes and the `δ`
gap; the arithmetic identities are proved. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FreyModularityShapeActual

/-- Frey discriminant `16·a²b²c²` in natural-number form. -/
def freyDelta (a b c : ℕ) : ℕ := 16 * a ^ 2 * b ^ 2 * c ^ 2

theorem freyDelta_eq_sixteen_mul_sq (a b c : ℕ) :
    freyDelta a b c = 16 * (a * b * c) ^ 2 := by
  unfold freyDelta
  ring

/-- Odd conductor shape: product over odd prime divisors of `a*b*c`. -/
def freyOddConductorShape (a b c : ℕ) : ℕ :=
  ∏ p ∈ (a * b * c).primeFactors.filter (fun p => p ≠ 2), p

theorem freyOddConductorShape_eq (a b c : ℕ) :
    freyOddConductorShape a b c =
      ∏ p ∈ (a * b * c).primeFactors.filter (fun p => p ≠ 2), p := rfl

/-- Tate parameter shape `q = j⁻¹`. -/
def freyTateQ (j : ℚ) : ℚ := j⁻¹

theorem freyTateQ_eq (j : ℚ) : freyTateQ j = j⁻¹ := rfl

/-- Modularity degree `δ` / conductor relation: the expected shape is
`N_Frey = δ² · (odd conductor) · 2^?`; no green theorem is available. -/
def ModularityDegreeShape (delta N_frey N_odd_conductor : ℕ) : Prop :=
  N_frey = delta ^ 2 * N_odd_conductor

theorem modularityDegreeShape_iff (delta N_frey N_odd_conductor : ℕ) :
    ModularityDegreeShape delta N_frey N_odd_conductor ↔
      N_frey = delta ^ 2 * N_odd_conductor := Iff.rfl

/-- The Frey discriminant's prime support is the support of `a*b*c` (green
`IsABCTriple.natRadical_freyDiscriminant_eq_natRadical_product`); recorded as
a shape predicate. -/
def FreySupportShape (a b c : ℕ) : Prop := 
  (freyDelta a b c).primeFactors = (a * b * c).primeFactors

def freyRows : List (String × String × String) :=
  [ ("Frey curve", "freyWeierstrassCurve / rationalFreyWeierstrassCurve", "GREEN (FreyWeierstrassCurve)"),
    ("discriminant", "Δ = 16*a^2*b^2*c^2 = 16*(abc)^2", "GREEN theorem + PROVED arithmetic (freyDelta_eq_sixteen_mul_sq)"),
    ("radical", "natRadical Δ = natRadical(abc); primeFactors Δ = primeFactors(abc)", "GREEN (FreyDiscriminantRadical)"),
    ("odd conductor", "oddConductor = ∏_{p|abc,p≠2} p; = oddRadical", "GREEN (FreyConductorOdd)"),
    ("Tate q", "q = j⁻¹; ||q|| = ||j||⁻¹; log-volume comparison packet", "GREEN (FreyTateParameterComparison)"),
    ("Tate summary", "freyTateComparisonPacket_summary", "GREEN"),
    ("modularity degree δ", "N_Frey = δ² * N_odd", "GAP (no green δ relation; only shape def)"),
    ("support shape", "primeFactors Δ = primeFactors abc", "DEF/GREEN cited") ]

theorem freyRows_length : freyRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyModularityShapeActual.freyDelta_eq_sixteen_mul_sq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyModularityShapeActual.freyOddConductorShape_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyModularityShapeActual.modularityDegreeShape_iff

end LeanFormal.IUT.XiFPaper.Mzk1FreyModularityShapeActual

end