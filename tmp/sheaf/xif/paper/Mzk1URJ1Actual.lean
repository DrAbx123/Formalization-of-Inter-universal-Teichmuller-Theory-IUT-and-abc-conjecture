/- U-R J1 (red-fix): actual q-root lattice, theta source span, and the q-reading
identities on the actual root extension.

The former version imported the non-actual `URPacketDefs` (`urVarpi := 1`)
and the failed `URThetaRegion`, and passed an extra packet argument to
`ur_qReading_formula`.  This version uses only the actual data of
`Mzk1URPacketActual` / `Mzk1URRootExtensionActual` / `Mzk1URThetaHullActual` and is
green.  The packet-hull containment is the generic actual-data statement of
`URThetaRegion` (see its docstring for the concrete-instantiation heartbeat
limitation). -/
import tmp.sheaf.xif.paper.Mzk1URPacketActual
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullActual
import tmp.sheaf.xif.paper.URThetaRegion
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1URJ1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1URPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual
open LeanFormal.IUT.XiFPaper.URThetaRegion
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- q-root lattice element is an integer multiple of the actual root datum. -/
theorem ur_qRootLattice_int (r : urBlock X) {x : urBlock X}
    (hx : x ∈ urQRootLattice X r) : ∃ n : ℤ, x = n • r := hx

/-- theta source span element is an actual integer combination of generators. -/
theorem ur_thetaSourceSpan_int (gens : Finset (urBlock X)) {x : urBlock X}
    (hx : x ∈ urThetaSourceSpan X gens) :
    ∃ c : urBlock X → ℤ, x = ∑ g ∈ gens, (c g) • g := hx

/-- q reading formula for the root parameter (no extra packet argument). -/
theorem ur_qReading_root_formula {p : Nat} {K : Type*} [NormedField K]
    (D : DistinguishedScalarData p K) :
    ord (K := K) p (theta D.alpha D.j) =
      ((D.j : Real) ^ 2 / (2 * (D.l : Real))) * ord (K := K) p D.q :=
  rootParameterWeight_eq_ord_varpi D

/-- Actual per-b q-pilot <= actual theta hull (accepted actual root-hull
containment on the actual T-side data). -/
theorem ur_perB_q_le_theta {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog T b ≤ perBThetaHullLog T b :=
  actualPerB_inequality T b

/-- Actual theta-pilot order bridge on the actual finite root extension: the
actual log-norm of `theta_j` is the route §5.2.2 shift (the C1 negative q term). -/
theorem ur_qReading_theta_order {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    Real.log ‖urRootTheta T b j‖ =
      -((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
        Real.log (qVFamTensorP T b : ℝ) :=
  urRootTheta_log_norm_eq_neg_shift (T := T) (b := b) j

#print axioms ur_qRootLattice_int
#print axioms ur_thetaSourceSpan_int
#print axioms ur_thetaRegion_subset_hull
#print axioms ur_qReading_root_formula
#print axioms ur_perB_q_le_theta
#print axioms ur_qReading_theta_order

end LeanFormal.IUT.XiFPaper.Mzk1URJ1Actual
end