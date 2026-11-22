import tmp.sheaf.xif.paper.Mzk1A1InverseLatticeNormActual
import tmp.sheaf.xif.paper.Mzk1A1LatticeValuationActual
/-! #A1.5/A1.6 actual qhat/J_s identification: compose the actual norm description
with the generic inverse-lattice saturation theorem.

`mem_lambdaLattice_iff`/`mem_qhatLattice_iff` identify the actual lattices with
norm balls.  If the lambda-lattice is recognized as the principal valuation
lattice `{y | m <= b y}` (the valuation/ramification datum), then the actual
inverse lambda-lattice is exactly the saturated lattice `{x | ceilDiv m e <= a x}`.
No hscale/hid hypothesis is added; the only input is the principal-lattice
recognition of the valuation order. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationIdentifyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1InverseLatticeNormActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Actual inverse lambda-lattice as the inverse image of the principal
valuation lattice. -/
theorem inverseLambdaLattice_eq_inverseLattice
    (bval : ↑(rootNormedExtension T b) -> Nat) (m : Nat)
    (hLambda : lambdaLattice T b = principalLattice bval m) :
    inverseLambdaLattice T b =
      inverseLattice (fun x : rootBase T b =>
        algebraMap (rootBase T b) (↑(rootNormedExtension T b)) x) bval m := by
  unfold inverseLambdaLattice inverseLattice
  rw [hLambda]
/-- Decisive A1.5/A1.6 identification: under the principal-lattice recognition
and the ramification identity `b(iota x)=e*a x`, the actual inverse lambda-lattice
is the saturated lattice. -/
theorem inverseLambdaLattice_eq_saturated_actual
    (aval : rootBase T b -> Nat) (bval : ↑(rootNormedExtension T b) -> Nat)
    (m e : Nat) (he : 0 < e)
    (hram : ∀ x : rootBase T b,
      bval (algebraMap (rootBase T b) (↑(rootNormedExtension T b)) x) =
        e * aval x)
    (hLambda : lambdaLattice T b = principalLattice bval m) :
    inverseLambdaLattice T b = saturatedLattice aval m e := by
  rw [inverseLambdaLattice_eq_inverseLattice T b bval m hLambda]
  exact inverseLattice_eq_saturated _ aval bval e he m hram
end LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationIdentifyActual
end