import tmp.sheaf.xif.paper.S3133ExistingModelAdaptationActual
import tmp.sheaf.xif.paper.S3135ModelSkeletonInterfaceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import Mathlib.Tactic

noncomputable section
open scoped BigOperators NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: tree-model + CardHull consumption in the first-triangle composition (reuse)

Consumes, without rebuilding:
* the EXISTING tree model via S3133ExistingModelAdaptationActual (which is itself
  the approved adaptation layer over SourceUnitRegionHaarDataActual):
  S3133TreeModelInput / Realization / HaarData, scaling = 1, theta q = 1;
* the StepXI/CardHull signed hull layer (CardHullRealSignedLogVolume):
  the (xi-f) direction -|log(Theta)| <= -(image-union log-volume) for the tree's
  realized hull, i.e. the in-model fourth-triangle hull side.

The bundled record SourceModelRouteEvidence collects these in-model evidences so
the route composition can name them in its residual list (Option-B).

**Component, not paper object.**  Registry frozen 13129; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139HaarModelConsumptionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual
open LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The tree model's Haar datum scaling is the monoid unit (reused theorem). -/
theorem s3139_treeModelHaarData_scaling
    (S : SourceDefinition31Data.{0} l) (n : ThetaPilotCarrier l) :
    (S3133TreeModelHaarData S n).scaling = 1 :=
  S3133TreeModelHaarData_scaling S n

/-- The tree model's theta q-parameter is 1 at every index (reused theorem). -/
theorem s3139_treeModel_theta_q
    (S : SourceDefinition31Data.{0} l) (n m : Int) :
    ((S3133TreeModelInput S).theaterAt n m).thetaPacket.q = 1 :=
  S3133TreeModel_theta_q S n m

/-- In-model fourth-triangle hull side: the signed hull log-volume is at most the
signed image-union log-volume ((xi-f) direction, proven in-tree via CardHull). -/
theorem s3139_modelHullVolume_le_imageVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedHullLogVolume v R n ≤ I.sourceSignedImageLogVolume v R n :=
  sourceSignedHullLogVolume_le_sourceSignedImageLogVolume I v R n hfin

/-- The in-model route evidence bundle: tree-model Haar/theta data plus the
CardHull (xi-f) direction plus the model Haar scaling interface. -/
structure SourceModelRouteEvidence
    (S : SourceDefinition31Data.{0} l) (n : ThetaPilotCarrier l)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (hfin : I.sourceHullVolume v R n < ⊤) where
  /-- the tree-model Haar datum scaling equals 1 -/
  haar_scaling_one : (S3133TreeModelHaarData S n).scaling = 1
  /-- the tree-model theta q-parameter is 1 -/
  theta_q_one : ((S3133TreeModelInput S).theaterAt 1 0).thetaPacket.q = 1
  /-- the in-model (xi-f) direction from the CardHull layer -/
  hull_le_image :
    I.sourceSignedHullLogVolume v R n ≤ I.sourceSignedImageLogVolume v R n

/-- The in-model route evidence is constructible by reuse (no new mathematical
input): tree model Haar/theta theorems plus the CardHull theorem. -/
def sourceModelRouteEvidence
    (S : SourceDefinition31Data.{0} l) (n : ThetaPilotCarrier l)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (hfin : I.sourceHullVolume v R n < ⊤) :
    SourceModelRouteEvidence S n I v R hfin where
  haar_scaling_one := s3139_treeModelHaarData_scaling S n
  theta_q_one := s3139_treeModel_theta_q S 1 0
  hull_le_image := s3139_modelHullVolume_le_imageVolume I v R n hfin

end LeanFormal.IUT.XiFPaper.S3139HaarModelConsumptionActual

end
