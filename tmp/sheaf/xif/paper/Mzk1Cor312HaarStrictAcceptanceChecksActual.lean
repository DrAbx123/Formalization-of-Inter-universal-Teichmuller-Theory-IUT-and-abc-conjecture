/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312UnconditionalStrictAcceptanceActual

/-!
# A553 checks: annulus measure resolution of strict_measure

Machine checks of the unconditional acceptance path:
* the q-ball region has positive and finite normalized Haar measure;
* the annulus strictness gives the strict normalized real-volume increase;
* `strict_measure` of the requirement is the PROVED annulus theorem;
* the only assumptions are the geometric side conditions (`hstrict`,`hqpos`,`hultra`,
  `b0`, hull finiteness), not the comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312HaarStrictAcceptanceChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312UnconditionalStrictAcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The q-ball has positive product Haar measure. -/
theorem qBall_haar_pos (G : HaarStrictGeometry T) :
    0 < rootExtensionProductHaar T (qBallRegion T) :=
  qBallRegion_measure_pos T G.hstrict G.hqpos

/-- The q-ball has finite product Haar measure. -/
theorem qBall_haar_lt_top (G : HaarStrictGeometry T) :
    rootExtensionProductHaar T (qBallRegion T) < ⊤ :=
  qBallRegion_measure_lt_top T G.hstrict G.hqpos

/-- The annulus strictness in product Haar form (re-export). -/
theorem qBall_hull_haar_strict (G : HaarStrictGeometry T) :
    rootExtensionProductHaar T (qBallRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  rootExtensionProductHaar_haarStrict T G.hstrict G.hqpos G.hultra G.b0

/-- The normalized real volume of the q-ball is positive. -/
theorem qBall_normalizedRealVolume_pos (G : HaarStrictGeometry T) :
    0 < normalizedRealVolume T (qBallRegion T) :=
  normalizedRealVolume_qBall_pos T G

/-- `strict_measure` of the unconditional requirement is the PROVED annulus theorem. -/
theorem strict_measure_is_annulus (G : HaarStrictGeometry T) :
    (unconditionalRequirement T G).strict_measure =
      normalizedRealVolume_strict T G :=
  rfl

/-- **Accounting**: q-pos and strict measure are theorems; the remaining assumptions
  are only the geometric side conditions. -/
theorem annulus_accounting (G : HaarStrictGeometry T) :
    (0 < normalizedRealVolume T (qBallRegion T)) ∧
      (normalizedRealVolume T (qBallRegion T) < normalizedRealVolume T (s1902Hull T)) ∧
      (rootExtensionProductHaar T (qBallRegion T) <
        rootExtensionProductHaar T (s1902Hull T)) :=
  ⟨qBall_normalizedRealVolume_pos T G, normalizedRealVolume_strict T G,
   qBall_hull_haar_strict T G⟩

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312HaarStrictAcceptanceChecksActual