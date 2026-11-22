/- R1-I exchange square (kurt): q-lattice / Theta lattice masses on the SAME actual root carrier.

Uses the DONE donors:
  Mzk1URRootExtensionActual.urRootAlpha_pow : urRootAlpha^(2l) = algebraMap q
  Mzk1URRootExtInstancesActual.urRootAlpha_mass_order : (1/[L:Qp]) (log mu(r O)-log mu(O)) = -(1/(2l)) ord_p(q) log p
  Mzk1URRootExtInstancesActual.urRootTheta_mass / urRootTheta_log_norm_eq_q
  Mzk1URBadPlaceActualMapActual.badPlaceCoeff / badPlaceQRegion_nu
Statements: the transport counts 1/(2l) EXACTLY ONCE, and every Theta lattice mass is an integral
(gaussExponent) multiple of the root lattice mass -- i.e. the q/Theta rows are the same lattice
row up to the gauss power (the exchange square at mass level).
-/
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import tmp.sheaf.xif.paper.Mzk1URBadPlaceActualMapActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URRootExchangeSquareActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.Mzk1URBadPlaceActualMapActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The root lattice mass equals the half of the q-block lattice mass: 1/(2l) appears once. -/
theorem rootMass_eq_half_blockMass :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootAlpha T b) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      (1 / (2 * (l.value : ℝ))) *
        (-(badPlaceCoeff (T := T) (b := b)) * Real.log (qVFamTensorP T b : ℝ)) := by
  rw [urRootAlpha_mass_order]
  unfold badPlaceCoeff
  ring

/-- The Theta lattice mass of label j is the gaussExponent-multiple of the root lattice mass
(the exchange square at mass level: q row and Theta row are the same lattice row up to r^j). -/
theorem thetaMass_eq_gauss_mul_alphaMass (j : SignedLabel l.value) :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
      (Real.log (rootExtensionHaar T b
          ((urRootTheta T b j) • (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b)))).toReal -
        Real.log (rootExtensionHaar T b
          (Integers (rootNormedExtension T b) :
            Set (rootNormedExtension T b))).toReal) =
      (gaussExponent j.1 : ℝ) *
        ((1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ)) *
          (Real.log (rootExtensionHaar T b
              ((urRootAlpha T b) • (Integers (rootNormedExtension T b) :
                Set (rootNormedExtension T b)))).toReal -
            Real.log (rootExtensionHaar T b
              (Integers (rootNormedExtension T b) :
                Set (rootNormedExtension T b))).toReal)) := by
  rw [urRootTheta_mass, urRootAlpha_mass, urRootTheta_log_norm_eq_q]
  ring


#print axioms rootMass_eq_half_blockMass
#print axioms thetaMass_eq_gauss_mul_alphaMass

end LeanFormal.IUT.XiFPaper.Mzk1URRootExchangeSquareActual
end