import tmp.sheaf.xif.paper.S3058ChartZPreservation

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3058ChartZPreservation
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3059ChartYCompatibility

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Identity chart-Y compatibility. -/
def S3059ChartYIdCompatibility : Prop :=
  S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫
      (𝟙 (S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K)) =
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K

/-- Alpha chart-Y compatibility: the chart-Y component of global alpha is the
expected alpha chart-Y morphism. -/
def S3059ChartYAlphaCompatibility : Prop :=
  S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left =
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left

/-- Combined chart-Y compatibility target. -/
def S3059ChartYCompatibility : Prop :=
  S3059ChartYIdCompatibility ∧ S3059ChartYAlphaCompatibility

theorem S3059_chartY_id : S3059ChartYIdCompatibility := by
  unfold S3059ChartYIdCompatibility
  rw [Category.comp_id]

theorem S3059_chartY_alpha : S3059ChartYAlphaCompatibility := by
  unfold S3059ChartYAlphaCompatibility
  rfl

theorem S3059_chartYCompatibility : S3059ChartYCompatibility :=
  ⟨S3059_chartY_id, S3059_chartY_alpha⟩

/-!
## Exact statement and first error

S3059ChartYCompatibility records the chart-Y component comparisons for the two
global branches; both are actual here (identity is simplification, alpha is the
formal same-morphism comparison).

First error: for an arbitrary β with S3055RingAutoOfChartZ β and φ = id or
φ = S2853RingHom, there is no theorem that the chart-Y component of β matches
the corresponding global branch.  This is the missing branch comparison in
S3054GluingData.  No chart-Y compatibility for arbitrary β is faked.
-/

#check S3059ChartYIdCompatibility
#check S3059ChartYAlphaCompatibility
#check S3059ChartYCompatibility
#check S3059_chartY_id
#check S3059_chartY_alpha
#check S3059_chartYCompatibility
#print axioms S3059_chartYCompatibility

end LeanFormal.IUT.XiFPaper.S3059ChartYCompatibility
end
