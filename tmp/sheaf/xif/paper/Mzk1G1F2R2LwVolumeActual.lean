/- PIECE 3: L_w local root ball scalar for hread.
   From Mzk1G1F2R2LocalStepVActual.localRootLogVolume_eq_order:
     localRootLogVolume = -((1/(2l)) * localNormOrder * log p).
   Under the order identification localNormOrder = cP (paper local coefficient, v/e_abs),
   this is exactly -(cP/(2l)) * log p. The paper-Theta readout equals it under the
   explicit readout bridge hread. No fake identification; bridges are hypotheses. -/
import tmp.sheaf.xif.paper.Mzk1G1F2R2LocalStepVActual
import tmp.sheaf.xif.paper.Mzk1ULR0RealDictionaryActual
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LocalStepVActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
open LeanFormal.IUT.LocalFieldLogarithm
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- PIECE 3a: order identification => localRootLogVolume = -(cP/(2l)) log p. -/
theorem localRootLogVolume_eq_neg_cP_logp
    (b : Bad (nativePlaceSelection T))
    (hord : (localNormOrder (qVFamTensorP T b)
        (((sourceRootQUnit T b) : (rootBase T b)ˣ) : rootBase T b) : Real) = cP (l := l) T b) :
    localRootLogVolume (T := T) (b := b) =
      - (cP (l := l) T b / (2 * (l.value : Real))) * Real.log (qVFamTensorP T b : Real) := by
  rw [localRootLogVolume_eq_order, hord]
  ring

/-- PIECE 3b: the paper-Theta per-b readout equals -(cP/(2l)) log p
    under the readout bridge and the order identification. -/
theorem paperThetaReadoutB_eq_neg_cP_logp
    (b : Bad (nativePlaceSelection T))
    (hread : paperThetaReadoutB (l := l) T b =
      localRootLogVolume (T := T) (b := b))
    (hord : (localNormOrder (qVFamTensorP T b)
        (((sourceRootQUnit T b) : (rootBase T b)ˣ) : rootBase T b) : Real) = cP (l := l) T b) :
    paperThetaReadoutB (l := l) T b =
      - (cP (l := l) T b / (2 * (l.value : Real))) * Real.log (qVFamTensorP T b : Real) := by
  rw [hread, localRootLogVolume_eq_neg_cP_logp (T := T) b hord]

#print axioms localRootLogVolume_eq_neg_cP_logp
#print axioms paperThetaReadoutB_eq_neg_cP_logp

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwVolumeActual