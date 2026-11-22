import Mathlib
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionStepProviderActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionBetaTrackingActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionBaseCaseActual
import LeanFormal.IUT.Audit.Status

/-!
# Mzk1NestedInductionBetaTrackingGeometricActual — geometric data => β-tracking provider

STEP 0 prior-art: Mzk1NestedInductionStepProviderActual.stepTransport_of_goal (target
transport along f0, proved conditional on CVCompositionLawF); our beta-tracking provider
form (Mzk1NestedInductionBetaTrackingActual).  This file isolates the exact geometric
data the paper's step must supply (q = normalised f0, S' = step set, β' = f0 β,
S'⊆ step image, critical images in S', avoidance, measure decrease) and PROVES that this
data (plus the CV composition law) implies the β-tracking provider.  The construction of
the data remains NAMED.

No closure claim; registry frozen 14041.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBetaTrackingGeometricActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBetaTrackingActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseCaseActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- **Exact geometric step data** (paper Lemma 2.4 lines 195-206, normalised f0 step):
a nonconstant polynomial q over Q̄, a finite next set S', the image/critical image
membership, the avoidance f0(β) ∉ S' for all β ∉ S, and the lex (maxDegP,numMaxP)
decrease. -/
structure BetaTrackingGeometricData (S : Finset (P1Point (AlgebraicClosure ℚ))) where
  q : Polynomial (AlgebraicClosure ℚ)
  hqpos : 0 < q.natDegree
  S' : Finset (P1Point (AlgebraicClosure ℚ))
  hmap : ∀ p ∈ S, f0Map q p ∈ S'
  hcvS : ∀ z : AlgebraicClosure ℚ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
    P1Point.ofFinite (Polynomial.aeval z q) ∈ S'
  havoid : ∀ β : P1Point (AlgebraicClosure ℚ), β ∉ S → f0Map q β ∉ S'
  hlex : Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S)

/-- Named geometric input: every state with maxDegP > 1 admits the step data. -/
def BetaTrackingGeometricInput : Prop :=
  ∀ S : Finset (P1Point (AlgebraicClosure ℚ)), 1 < maxDegP S →
    Nonempty (BetaTrackingGeometricData S)

/-- **REDUCTION (PROVED):** geometric step data + CV composition law imply the
β-tracking step provider, by the already-proved target transport along f0. -/
theorem betaTrackingStepProvider_of_geometric
    (hcv : CVCompositionLawF) (hgeom : BetaTrackingGeometricInput) :
    BetaTrackingStepProvider := by
  intro S hbig
  obtain ⟨d⟩ := hgeom S hbig
  refine ⟨d.S', d.hlex, ?_⟩
  intro β hβ
  exact ⟨f0Map d.q β, d.havoid β hβ,
    fun hgoal => stepTransport_of_goal hcv d.hqpos d.hmap d.hcvS hgoal⟩

/-- **END-TO-END (conditional):** base provider + CV composition law + geometric step
input give the paper-scope Lemma 2.4 statement. -/
theorem paperScopeLemma24Statement_of_geometric
    (hbase : ∀ (S : Finset (P1Point (AlgebraicClosure ℚ)))
      (β : P1Point (AlgebraicClosure ℚ)), β ∉ S → maxDegP S ≤ 1 →
        PaperScopeLemma24Target S β)
    (hcv : CVCompositionLawF) (hgeom : BetaTrackingGeometricInput) :
    PaperScopeLemma24Statement :=
  paperScopeLemma24Statement_of_betaTrackingProviders hbase
    (betaTrackingStepProvider_of_geometric hcv hgeom)

/-- **Base fully discharged:** baseCaseProvider_proved (identity polynomial, from
Mzk1NestedInductionBaseCaseActual) plugs into the base slot; only the CV composition law
and the geometric step data remain as hypotheses. -/
theorem paperScopeLemma24Statement_of_geometric_dischargedBase
    (hcv : CVCompositionLawF) (hgeom : BetaTrackingGeometricInput) :
    PaperScopeLemma24Statement :=
  paperScopeLemma24Statement_of_geometric baseCaseProvider_proved hcv hgeom

/-- Row record: reduction proved; construction named. -/
def betaTrackingGeometricRows : List (String × String × String) :=
  [ ("exact geometric step data", "DEFINED", "BetaTrackingGeometricData (q, S', image/critical membership, avoidance, lex decrease)")
  , ("geometric data -> beta-tracking provider", "PROVED", "betaTrackingStepProvider_of_geometric, using stepTransport_of_goal")
  , ("CV composition law", "REUSED (PROVED elsewhere)", "CVCompositionLawF; discharged by cvCompositionLawF_proved")
  , ("construction of the geometric data", "NAMED", "normalised f0 + analytic avoidance; the remaining Problem C step gap") ]

theorem betaTrackingGeometricRows_length : betaTrackingGeometricRows.length = 4 := rfl

#check BetaTrackingGeometricData
#check betaTrackingStepProvider_of_geometric
#check betaTrackingGeometricRows_length

end LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBetaTrackingGeometricActual
end
