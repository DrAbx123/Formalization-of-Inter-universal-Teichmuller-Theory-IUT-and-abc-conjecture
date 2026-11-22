import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceValues
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

/-!
# C7 source possible-image region and source hull

The actual C4 witnessed output region `U` is contained in the actual source
holomorphic hull.  This is source-side containment, not the IQ canonical hull.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7SourceU

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceValues

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- The actual source possible-image region at `(n,x)`. -/
def sourceU (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    Set (I.ThetaPilotPoint D.place.v) :=
  D.U n x

theorem sourceU_subset_sourceHolomorphicHull (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) :
    sourceU (D := D) n x ⊆ I.sourceHolomorphicHull D.place.v D.place.R n := by
  rintro y ⟨c, rfl⟩
  exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull D.place.v D.place.R n c

theorem sourceU_nonempty (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) :
    (sourceU (D := D) n x).Nonempty := by
  refine ⟨D.eval n x zeroSignedLabel, ?_⟩
  exact ⟨zeroSignedLabel, rfl⟩

theorem sourceValues_eq_image (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) :
    values (D := D) n x =
      I.sourceLocalLogDegree D.place.v '' sourceU (D := D) n x := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨D.eval n x c, ⟨c, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩

end LeanFormal.IUT.N8Closure.C7SourceU