import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
/-!
# P8-P (route §8.6): from the additive log-c bound (F9) to the uniform Frey
j-height criterion (F)

Route §8.6: after F6–F8 give
  `Real.log c ≤ (1+ε) * Real.log (radical (a*b*c)) + C_ε` for every primitive
ABC triple, the actual Frey j-height donor
  `Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤ 6 * Real.log c + Real.log 256`
yields the criterion with `B_ε = 6 * C_ε + Real.log 256`; then the existing
`abcConjecture_iff_freyJProductHeightCriterion` produces ABC.
Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FreyAssemblyActual

open LeanFormal.IUT

/-- Route §8.6 assembly (F9 → F). -/
theorem freyJProductHeightCriterion_of_logConjecture
    (h : ABCLogConjecture) : ABCFreyJProductHeightCriterion := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨6 * C + Real.log 256, ?_⟩
  intro a b c habc
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple habc
  have hlogc : Real.log (c : ℝ) ≤
      (1 + ε) * Real.log (radical (a * b * c) : ℝ) + C := hC a b c habc
  rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant habc]
  have hheight : Height.logHeight₁ (abcJInvariant a b c) ≤
      6 * Real.log (c : ℝ) + Real.log 256 := abcJInvariant_logHeight_le habc
  nlinarith

/-- Route §8.6 terminal map: criterion inhabitant gives ABC. -/
theorem abcConjecture_of_freyJProductHeightCriterion
    (h : ABCFreyJProductHeightCriterion) : ABCConjecture :=
  abcConjecture_iff_freyJProductHeightCriterion.mpr h

/-- Combined route §8.6 assembly: additive log-c bound implies ABC. -/
theorem abcConjecture_of_logConjecture (h : ABCLogConjecture) : ABCConjecture :=
  abcConjecture_of_freyJProductHeightCriterion
    (freyJProductHeightCriterion_of_logConjecture h)

end LeanFormal.IUT.XiFPaper.Mzk1P8FreyAssemblyActual
