import tmp.sheaf.xif.paper.S3066ChartYOverlapPreimageActual
import tmp.sheaf.xif.paper.S3065ChartYNonoverlapActual
import tmp.sheaf.xif.paper.S3062ChartZPreservationProof
import tmp.sheaf.xif.paper.S2828PointRealizationActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3066ChartYOverlapPreimageActual
open LeanFormal.IUT.XiFPaper.S3065ChartYNonoverlapActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2828PointRealizationActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3067PointRealizationActual

abbrev K := S3062ChartZPreservationProof.K
abbrev e := S2820E37TransitionIso K

/-- S3062PointRealization is actual: S3065 nonoverlap + S3066 overlap
preimage. -/
theorem S3067_pointRealization : S3062PointRealization :=
  S3065_pointRealization S3066_chartYOverlapPreimage

/-- Exact point-range inclusion needed for the open-immersion factorization:
if β maps every non-infinity point to a non-infinity point, then the composite
ChartZMap ≫ β has range inside ChartZMap. -/
def S3067ChartZRangeInclusion : Prop :=
  ∀ (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X),
    (∀ x : S3062ChartZPreservationProof.G,
      x ≠ S3062InfinityPoint → β.left x ≠ S3062InfinityPoint) →
      Set.range (E37ProjChartZMap K e ≫ β.left) ⊆
        Set.range (E37ProjChartZMap K e)

/-!
## Exact statements and first error

Actual:
* S3067_pointRealization: S3062PointRealization, from S3065 nonoverlap and
  S3066 overlap preimage.

First error: S3067ChartZRangeInclusion itself is not proved.  It needs the
point-set argument: for x in chart-Z, if β(x)=∞ then β^{-1}(∞)=∞ (∞-fixing),
so x=∞, contradicting x∈U_Z (∞∉U_Z).  The point realization (S3067) and
nonoverlap (S3065) are actual, but the bijectivity/preimage point lemma for
β is still missing.  No chart-Z factorization is faked.
-/

#check S3067_pointRealization
#check S3067ChartZRangeInclusion
#print axioms S3067_pointRealization

end LeanFormal.IUT.XiFPaper.S3067PointRealizationActual
end
