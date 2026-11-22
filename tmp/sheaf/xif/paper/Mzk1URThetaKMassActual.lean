/- J1-M Kummer mass via the accepted principal-lattice formula (kurt).

Lead ruling: replace the HaarScaleData / Haar-scaling route by the ACCEPTED principal-lattice
mass formula
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
(finite-place StepV assembly, IV Prop 1.4 (i)): for local generators ||g_i|| = p^{-c_i},
  mu_log((F c) * O_hol) = -((sum_i c_i) * log p).
The HaarScaleData structure of Mzk1URThetaKKummerMassActual is therefore NOT part of the main
chain (kept only as fallback source; docstring there marked accordingly by this file's header).

Reuse (search record):
* LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
  (ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:173) - exact mass formula;
* Mzk1URThetaKKummerMassActual.log_div_two_l / kummer_mass_algebra - the 2l-root log algebra;
* david Mzk1URThetaKKummerMassActual? no: thetaMWeight_mul_thetaLamWeight in Mzk1ULThetaMWeightActual.

Default heartbeats.
-/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKKummerMassActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators NNReal Padic

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKMassActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKKummerMassActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)]

/-- Principal-lattice mass on the K-side carrier: exact normalized log volume. -/
theorem principal_lattice_mass
    (c : qVFamTensorV → ℝ)
    (g : (i : qVFamTensorV) → CommonPrimeCompletion ((ksPlaces T b) i (ksTuple i)))
    (hg : ∀ i, ‖g i‖ = ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ) ^ (-(c i))) :
    arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
      MeasureTheory.Measure.addHaar
      (((arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple c *
        arithmeticTupleHolomorphicLattice (ksPlaces T b) ksTuple :
          Submodule ℤ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
            (ksBlock T b)) : Set (ksBlock T b))) =
      -((∑ i, c i) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
    (ksPlaces T b) ksTuple MeasureTheory.Measure.addHaar c g hg

/-- The 2l-root log algebra: with q = a^(2l), (1/(2l)) log q = log a. -/
theorem mass_root_algebra (a : ℝ) (ha : 0 < a) (ll : ℕ) (hl : 0 < ll) (q : ℝ)
    (hq : q = a ^ (2 * ll)) :
    (1 / (2 * (ll : ℝ))) * Real.log q = Real.log a :=
  kummer_mass_algebra a ha ll hl q hq

#print axioms principal_lattice_mass
#print axioms mass_root_algebra

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKMassActual
end