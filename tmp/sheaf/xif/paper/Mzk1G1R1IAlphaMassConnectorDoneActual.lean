/- R1-I connector: the actual Kummer root mass (urRootAlpha) equals the q-lattice region J_b
mass, and r^(2l)=q, matching paper III.3.12 / row L10378 / Fig3.8.

Reuse (DONE, trio):
* Mzk1URRootExtensionActual.urRootAlpha_pow
* Mzk1URRootExtInstancesActual.urRootAlpha_mass_order
* Mzk1URBadPlaceActualMapActual.badPlaceQRegion_nu  (PROVED: nu(J_b) = -badPlaceCoeff * log p)
No new root construction; no sorry.
-/
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import tmp.sheaf.xif.paper.Mzk1URBadPlaceActualMapActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1IAlphaMassConnectorDoneActual

open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.Mzk1URBadPlaceActualMapActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)]

/-- R1-I: (1/[L:Q_p]) log-mass of the root lattice r·O_L equals (1/(2l)) times the
normalized log-volume of the actual q-lattice region J_b. -/
theorem urRootAlpha_mass_eq_badPlaceQRegion_nu :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootAlpha T b) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      (1 / (2 * (l.value : ℝ))) *
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
          MeasureTheory.Measure.addHaar (badPlaceQRegion (T := T) (b := b)) := by
  rw [urRootAlpha_mass_order, badPlaceQRegion_nu]
  ring

/-- R1-I: the actual Kummer relation r^(2l)=q in the root carrier. -/
theorem urRootAlpha_pow_eq :
    (urRootAlpha T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (urRootCarrier T b)
        ((sourceRootQUnit T b : rootBase T b)) :=
  urRootAlpha_pow T b

#print axioms urRootAlpha_mass_eq_badPlaceQRegion_nu
#print axioms urRootAlpha_pow_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1R1IAlphaMassConnectorDoneActual
