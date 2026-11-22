import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCompleteActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1A8EvalFamilyActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCompleteActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- A8 actual rank-one evaluation family, using the existing actual `(b,label)`
label block.  The place and label are both kept. -/
noncomputable def evalTheta (b : Bad (nativePlaceSelection T))
    (label : SignedLabel l.value) :=
  p2BlockSourceTheta T ⟨b, label⟩

theorem evalTheta_eq_p2Block (b : Bad (nativePlaceSelection T))
    (label : SignedLabel l.value) :
    evalTheta T b label = p2BlockSourceTheta T ⟨b, label⟩ := rfl

theorem evalTheta_eq_actualLanding (b : Bad (nativePlaceSelection T))
    (label : SignedLabel l.value) :
    evalTheta T b label = p2BlockLanding T ⟨b, label⟩ := rfl

/-- The actual weighted log-evaluation sum over all signed labels at one bad
place. -/
noncomputable def weightedThetaLogSum (b : Bad (nativePlaceSelection T)) : Real :=
  ∑ label : SignedLabel l.value, Real.log ‖evalTheta T b label‖

/-- Relabel invariance of the actual weighted evaluation: reindexing the
signed labels by a permutation does not change the finite weighted sum. -/
theorem weightedThetaLogSum_perm (b : Bad (nativePlaceSelection T))
    (e : Equiv.Perm (SignedLabel l.value)) :
    weightedThetaLogSum T b =
      ∑ label : SignedLabel l.value, Real.log ‖evalTheta T b (e label)‖ := by
  unfold weightedThetaLogSum
  exact (Equiv.sum_comp e (fun label => Real.log ‖evalTheta T b label‖)).symm

#print axioms evalTheta_eq_p2Block
#print axioms weightedThetaLogSum_perm
end LeanFormal.IUT.XiFPaper.Mzk1A8EvalFamilyActual