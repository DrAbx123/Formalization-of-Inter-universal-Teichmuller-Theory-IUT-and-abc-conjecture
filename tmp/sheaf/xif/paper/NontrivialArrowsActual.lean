import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import tmp.sheaf.xif.paper.IPLAPTDataActual

/-! # Nontrivial actual Kummer/evaluation arrows between source strips

For the distinct actual source strips

  S00 = I.primeStripAt 0 0
  S01 = I.primeStripAt 0 1
  S10 = I.primeStripAt 1 0
  S11 = I.primeStripAt 1 1

this file constructs the strip-level representatives of

  SourceKummerArrow G S00 S01
  SourceEvaluationArrow G S01 S11

from the actual Hodge-theater links I.linkAt 0 0 0 1 and I.linkAt 0 1 1 1.

The production constructors sourceKummerArrowOfLayer and
sourceEvaluationArrowOfUnitPortion are then applied.  Their layer arguments
(SourceTimesMuKummerLayer and SourceEvaluationUnitPortion) are NOT constructed
by the frozen source record for distinct strips; they remain explicit fields.
No trivial/identity action, toy layer, axiom or sorry is inserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper
namespace NontrivialArrowsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Actual source strip S(0,0). -/
abbrev S00 : FPrimeStrip V := I.primeStripAt 0 0

/-- Actual source strip S(0,1). -/
abbrev S01 : FPrimeStrip V := I.primeStripAt 0 1

/-- Actual source strip S(1,0). -/
abbrev S10 : FPrimeStrip V := I.primeStripAt 1 0

/-- Actual source strip S(1,1). -/
abbrev S11 : FPrimeStrip V := I.primeStripAt 1 1

/-- Actual strip-level representative S(0,0) -> S(0,1) from the Hodge-theater
link at (n,m)=(0,0). -/
def kummerStripIso : FPrimeStripEquiv (S00 (I := I)) (S01 (I := I)) :=
  (I.linkAt 0 0 0 1).primeStripEquiv

/-- Actual strip-level representative S(0,1) -> S(1,1) from the Hodge-theater
link at (n,m)=(0,1). -/
def evaluationStripIso : FPrimeStripEquiv (S01 (I := I)) (S11 (I := I)) :=
  (I.linkAt 0 1 1 1).primeStripEquiv

/-- The exact missing Card LK layer for the distinct vertical Kummer arrow
S00 -> S01. -/
structure NontrivialKummerLayerData where
  layer : SourceTimesMuKummerLayer G (S00 (I := I)) (S01 (I := I))

/-- The exact missing Card EV unit portion for the distinct evaluation arrow
S01 -> S11. -/
structure NontrivialEvaluationLayerData where
  unitPortion : SourceEvaluationUnitPortion G
    (S01 (I := I)) (S11 (I := I))

/-- Production assembly of the actual Kummer arrow from the actual strip link
and the explicit missing layer. -/
def kummerArrowOfLayerData
    (D : NontrivialKummerLayerData (I := I) (G := G)) :
    SourceKummerArrow G (S00 (I := I)) (S01 (I := I)) :=
  sourceKummerArrowOfLayer (kummerStripIso (I := I)) D.layer

/-- Production assembly of the actual evaluation arrow from the actual strip
link and the explicit missing unit portion. -/
def evaluationArrowOfLayerData
    (D : NontrivialEvaluationLayerData (I := I) (G := G)) :
    SourceEvaluationArrow G (S01 (I := I)) (S11 (I := I)) :=
  sourceEvaluationArrowOfUnitPortion (evaluationStripIso (I := I)) D.unitPortion

/-- Combined nontrivial arrow packet. -/
structure NontrivialArrowsActual where
  kummerData : NontrivialKummerLayerData (I := I) (G := G)
  evaluationData : NontrivialEvaluationLayerData (I := I) (G := G)

namespace NontrivialArrowsActual

variable (P : NontrivialArrowsActual (I := I) (G := G))

/-- The actual constructed Kummer arrow. -/
def kummer : SourceKummerArrow G (S00 (I := I)) (S01 (I := I)) :=
  kummerArrowOfLayerData P.kummerData

/-- The actual constructed evaluation arrow. -/
def evaluation : SourceEvaluationArrow G (S01 (I := I)) (S11 (I := I)) :=
  evaluationArrowOfLayerData P.evaluationData

/-- The Kummer strip representative is the actual source link. -/
@[simp] theorem kummer_stripIso :
    P.kummer.stripIso = kummerStripIso (I := I) := rfl

/-- The evaluation strip representative is the actual source link. -/
@[simp] theorem evaluation_stripIso :
    P.evaluation.stripIso = evaluationStripIso (I := I) := rfl

/-- The Kummer layer is the supplied explicit layer. -/
@[simp] theorem kummer_layer :
    P.kummer.layer = P.kummerData.layer := rfl

/-- The evaluation unit portion is the supplied explicit portion. -/
@[simp] theorem evaluation_unitPortion :
    P.evaluation.unitPortion = P.evaluationData.unitPortion := rfl

end NontrivialArrowsActual

/-! ## Exact missing layer data

The actual strip links kummerStripIso and evaluationStripIso are constructed
from I.linkAt.  The production constructors need the following source data,
which the frozen source record does not supply for the distinct strips:

1. SourceTimesMuKummerLayer G S00 S01:
   - actual G-actions sourceAction and targetAction on the strip units;
   - the Card LK Kummer isomorphism between the times-mu layers;
   - the equivariance/Kummer-isometry law.
2. SourceEvaluationUnitPortion G S01 S11:
   - actual G-actions on the unit groups of S01 and S11;
   - the Card EV unit-layer isomorphism;
   - the equivariance law of Theorem 3.11, (iii), (c).

The production provider KappaOrbitUnitsActionPairDatum.layerKummer can build
the Card LK layer only after a pair datum (source units, actions, factors and
kappa representatives) is supplied; no such datum exists for these distinct
strips in the frozen source.  Therefore no unconditional arrow is constructed
and no identity/trivial layer is inserted. -/

end NontrivialArrowsActual
end XiFPaper
end LeanFormal.IUT

end
