import tmp.sheaf.xif.paper.Mzk1A1LatticeValuationIdentifyActual
import tmp.sheaf.xif.paper.Mzk1A1LatticeInverseActual
import tmp.sheaf.xif.paper.Mzk1A1DeltaExplicitActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
/-! #A1.6 actual qhat saturation readout: under the principal-lattice
recognition and the ramification identity, the actual qVFamily element lies in
the saturated lattice, and the signed readout is `log||lambda|| - delta`. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1A1QhatSaturationReadoutActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationIdentifyActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationActual
open LeanFormal.IUT.XiFPaper.Mzk1A1InverseLatticeNormActual
open LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- The actual qVFamily element lies in the saturated valuation lattice. -/
theorem qVFamily_mem_saturatedLattice
    (aval : rootBase T b -> Nat) (bval : ↑(rootNormedExtension T b) -> Nat)
    (m e : Nat) (he : 0 < e)
    (hram : ∀ x : rootBase T b,
      bval (algebraMap (rootBase T b) (↑(rootNormedExtension T b)) x) =
        e * aval x)
    (hLambda : lambdaLattice T b = principalLattice bval m) :
    ((qVFamily T b).q : rootBase T b) ∈ saturatedLattice aval m e := by
  have hid := inverseLambdaLattice_eq_saturated_actual
    (T := T) (b := b) aval bval m e he hram hLambda
  have hmem := qVFamily_mem_inverseLambdaLattice (T := T) (b := b)
  rw [hid] at hmem
  exact hmem
/-- A1.6 final signed readout: the actual qhat normalized log difference equals
`log||lambda|| - delta`. -/
theorem signedReadout_eq_log_radius_sub_delta :
    a1SignedTerm (T := T) (b := b) =
      Real.log (rootImageRadius T b : Real) - a1Delta (T := T) (b := b) := by
  exact a1SignedTerm_eq_log_radius_sub_delta (T := T) (b := b)
end LeanFormal.IUT.XiFPaper.Mzk1A1QhatSaturationReadoutActual
end