import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantRadicalBridge
import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison

/-!
# ABC as a uniform height criterion for the actual elliptic models

The criteria below retain the quantifiers of the ABC conjecture: for every
positive real epsilon there must be one real constant that works for every
positive primitive ABC triple.  The heights are Mathlib's canonical heights
of the actual Frey or Legendre curve's j-invariant.

These are equivalence theorems.  They do not prove any of the uniform upper
bounds, and they do not assume that an IUT estimate has been established.
-/

namespace LeanFormal.IUT

/-- The uniform j-height criterion for the actual Frey model, initially
expressed using the radical of the original ABC product. -/
def ABCFreyJProductHeightCriterion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ bound : ℝ,
    ∀ (a b c : ℕ) (h : IsABCTriple a b c),
      letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * (1 + epsilon) * Real.log (radical (a * b * c) : ℝ) + bound

/-- The same product-radical criterion for the actual Legendre curve at
the rational point `a/c`. -/
def ABCLegendreJProductHeightCriterion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ bound : ℝ,
    ∀ (a b c : ℕ) (h : IsABCTriple a b c),
      letI := abcRationalPoint_legendre_isElliptic h
      Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤
        6 * (1 + epsilon) * Real.log (radical (a * b * c) : ℝ) + bound

/-- The desired denominator-radical criterion for the actual Frey curve.
The denominator is the reduced denominator of the actual rational
invariant, and the additive constant is independent of the ABC triple. -/
def ABCFreyJDenominatorHeightCriterion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ bound : ℝ,
    ∀ (a b c : ℕ) (h : IsABCTriple a b c),
      letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * (1 + epsilon) *
          Real.log (radical (abcJInvariant a b c).den : ℝ) + bound

/-- The denominator-radical criterion for the actual Legendre curve.
It uses the same actual reduced rational invariant on the right. -/
def ABCLegendreJDenominatorHeightCriterion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ bound : ℝ,
    ∀ (a b c : ℕ) (h : IsABCTriple a b c),
      letI := abcRationalPoint_legendre_isElliptic h
      Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j ≤
        6 * (1 + epsilon) *
          Real.log (radical (abcJInvariant a b c).den : ℝ) + bound

/-- The actual ABC conjecture is equivalent to the uniform Frey j-height
bound with the original product radical.  The forward constant is
`6*A + log 256`; the reverse constant is `(B-log (27/64))/6`. -/
theorem abcConjecture_iff_freyJProductHeightCriterion :
    ABCConjecture ↔ ABCFreyJProductHeightCriterion := by
  rw [abcConjecture_iff_abcLogConjecture]
  constructor
  · intro habc epsilon hepsilon
    obtain ⟨constant, hconstant⟩ := habc epsilon hepsilon
    refine ⟨6 * constant + Real.log 256, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    have hcoordinate : Real.log (c : ℝ) ≤
        (1 + epsilon) * Real.log (radical (a * b * c) : ℝ) + constant :=
      hconstant a b c h
    rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant h]
    have hheight := abcJInvariant_logHeight_le h
    nlinarith
  · intro hfrey epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hfrey epsilon hepsilon
    refine ⟨(bound - Real.log (27 / 64 : ℝ)) / 6, ?_⟩
    change ∀ (a b c : ℕ), IsABCTriple a b c →
      Real.log (c : ℝ) ≤ (1 + epsilon) *
        Real.log (radical (a * b * c) : ℝ) + (bound - Real.log (27 / 64 : ℝ)) / 6
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    have hmodel := hbound a b c h
    rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant h] at hmodel
    have hheight := abcJInvariant_logHeight_ge h
    nlinarith

/-- Switching between these two actual model criteria preserves the
same additive constant, because their j-invariants have the same proved
rational expression.  No curve isomorphism is used. -/
theorem freyJProductHeightCriterion_iff_legendreJProductHeightCriterion :
    ABCFreyJProductHeightCriterion ↔ ABCLegendreJProductHeightCriterion := by
  constructor
  · intro hfrey epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hfrey epsilon hepsilon
    refine ⟨bound, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    letI := abcRationalPoint_legendre_isElliptic h
    have hmodel := hbound a b c h
    rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant h] at hmodel
    rw [abcRationalPoint_legendre_j_eq_abcJInvariant h]
    exact hmodel
  · intro hlegendre epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hlegendre epsilon hepsilon
    refine ⟨bound, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    letI := abcRationalPoint_legendre_isElliptic h
    have hmodel := hbound a b c h
    rw [abcRationalPoint_legendre_j_eq_abcJInvariant h] at hmodel
    rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant h]
    exact hmodel

/-- The product-radical criterion for the actual Legendre model is
equivalent to the original ABC conjecture. -/
theorem abcConjecture_iff_legendreJProductHeightCriterion :
    ABCConjecture ↔ ABCLegendreJProductHeightCriterion :=
  abcConjecture_iff_freyJProductHeightCriterion.trans
    freyJProductHeightCriterion_iff_legendreJProductHeightCriterion

/-- The equality of the actual j-invariants also identifies the two
denominator-radical criteria, with no change in the uniform constant. -/
theorem freyJDenominatorHeightCriterion_iff_legendreJDenominatorHeightCriterion :
    ABCFreyJDenominatorHeightCriterion ↔ ABCLegendreJDenominatorHeightCriterion := by
  constructor
  · intro hfrey epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hfrey epsilon hepsilon
    refine ⟨bound, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    letI := abcRationalPoint_legendre_isElliptic h
    have hmodel := hbound a b c h
    rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant h] at hmodel
    rw [abcRationalPoint_legendre_j_eq_abcJInvariant h]
    exact hmodel
  · intro hlegendre epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hlegendre epsilon hepsilon
    refine ⟨bound, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    letI := abcRationalPoint_legendre_isElliptic h
    have hmodel := hbound a b c h
    rw [abcRationalPoint_legendre_j_eq_abcJInvariant h] at hmodel
    rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant h]
    exact hmodel

/-- Replacing the original product radical by the actual reduced
j-denominator radical changes the uniform constant by at most
`6*(1+epsilon)*log 2`.  The reverse implication keeps the constant.
The coefficient is nonnegative because the original quantifier retains
the hypothesis `0 < epsilon`. -/
theorem freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion :
    ABCFreyJProductHeightCriterion ↔ ABCFreyJDenominatorHeightCriterion := by
  constructor
  · intro hproduct epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hproduct epsilon hepsilon
    refine ⟨bound + 6 * (1 + epsilon) * Real.log 2, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    have hcoefficient : 0 ≤ 6 * (1 + epsilon) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left
      h.abcInvariant_product_logRadical_le_den_add_log_two hcoefficient
    calc
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
          6 * (1 + epsilon) * Real.log (radical (a * b * c) : ℝ) + bound :=
        hbound a b c h
      _ ≤ 6 * (1 + epsilon) *
          (Real.log (radical (abcJInvariant a b c).den : ℝ) + Real.log 2) + bound :=
        add_le_add_left hscaled bound
      _ = 6 * (1 + epsilon) *
          Real.log (radical (abcJInvariant a b c).den : ℝ) +
            (bound + 6 * (1 + epsilon) * Real.log 2) := by ring
  · intro hdenominator epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hdenominator epsilon hepsilon
    refine ⟨bound, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    have hcoefficient : 0 ≤ 6 * (1 + epsilon) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left
      h.abcJInvariant_den_logRadical_le_product hcoefficient
    exact (hbound a b c h).trans (add_le_add_left hscaled bound)

/-- The actual ABC conjecture is equivalent to the stated uniform
canonical j-height estimate for the actual rational Frey model, using
the radical of the actual reduced j-denominator. -/
theorem abcConjecture_iff_freyJDenominatorHeightCriterion :
    ABCConjecture ↔ ABCFreyJDenominatorHeightCriterion :=
  abcConjecture_iff_freyJProductHeightCriterion.trans
    freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion

/-- The same exact ABC equivalence for the actual Legendre curve at
`a/c`.  The uniform estimate remains an equivalent assertion to be
proved, rather than an assumed consequence of IUT. -/
theorem abcConjecture_iff_legendreJDenominatorHeightCriterion :
    ABCConjecture ↔ ABCLegendreJDenominatorHeightCriterion :=
  abcConjecture_iff_freyJDenominatorHeightCriterion.trans
    freyJDenominatorHeightCriterion_iff_legendreJDenominatorHeightCriterion

end LeanFormal.IUT
