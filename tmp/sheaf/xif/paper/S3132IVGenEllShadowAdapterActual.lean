import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source-adapted IV / GenEll interface shadow (from vendor promachina)

Adapted (source reference only; not imported) from
vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/IUTStage1IUTIVAlgebra.lean:9887-9928
(`IUTStage1IUTIVCorollary23DiophantineInequalityShadow`).  The vendor record keeps
the exact GenEll form as an explicit field (`genEll_transfer`); we re-declare the
shape so the paper-route Theta comparison can be packaged with the same IV §2
interface fields.  Real declarations only; the GenEll statement itself is NOT
proved here (it is the exact hypothesis/transfer field of the source).
-/

namespace LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual

/-- Adapted IV Corollary 2.3 Diophantine-inequality shadow with the exact GenEll
transfer field (source-reference adaptation, vendor IUTStage1IUTIVAlgebra:9887). -/
structure AdaptedIVGenEllShadow (Point : Type*) where
  /-- the integer degree `d` -/
  d : ℕ
  d_pos : 0 < d
  /-- the "epsilon" of the generalized-elliptic statement -/
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  /-- hyperbolic curve input (source-level proposition) -/
  hyperbolicCurve : Prop
  hyperbolic_curve : hyperbolicCurve
  /-- height function -/
  height : Point → ℝ
  /-- log-differentiant -/
  logDiff : Point → ℝ
  /-- log-conductor -/
  logCond : Point → ℝ
  /-- [GenEll] Theorem 2.1 compact-subset input -/
  compactSubsetTheoremA : Prop
  compact_subset_theoremA : compactSubsetTheoremA
  /-- The exact GenEll transfer: the IV §2 inequality on a compact subset. -/
  genEll_transfer : compactSubsetTheoremA →
    ∃ lowerBound : ℝ,
      ∀ x : Point,
        lowerBound ≤ (1 + epsilon) * (logDiff x + logCond x) - height x

namespace AdaptedIVGenEllShadow

variable {Point : Type*}

/-- The IV §2 discrepancy form at a point. -/
noncomputable def discrepancy (data : AdaptedIVGenEllShadow Point) (x : Point) : ℝ :=
  (1 + data.epsilon) * (data.logDiff x + data.logCond x) - data.height x

/-- Existence of a lower bound for the discrepancy (GenEll transfer). -/
theorem exists_lowerBound (data : AdaptedIVGenEllShadow Point) :
    ∃ lowerBound : ℝ, ∀ x : Point, lowerBound ≤ data.discrepancy x := by
  obtain ⟨L, hL⟩ := data.genEll_transfer data.compact_subset_theoremA
  exact ⟨L, fun x => by simpa [discrepancy] using hL x⟩

/-- A chosen lower bound for the discrepancy. -/
noncomputable def lowerBound (data : AdaptedIVGenEllShadow Point) : ℝ :=
  Classical.choose data.exists_lowerBound

/-- The chosen lower bound is certified. -/
theorem discrepancy_bounded_below (data : AdaptedIVGenEllShadow Point) (x : Point) :
    data.lowerBound ≤ data.discrepancy x :=
  Classical.choose_spec data.exists_lowerBound x

end AdaptedIVGenEllShadow

#check AdaptedIVGenEllShadow
#check AdaptedIVGenEllShadow.exists_lowerBound
#check AdaptedIVGenEllShadow.lowerBound
#check AdaptedIVGenEllShadow.discrepancy_bounded_below

end LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual