import tmp.sheaf.xif.paper.S1225SourceChoiceCoreActual
noncomputable section
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
namespace Probe
variable {l : PrimeGeFive} {V : Type uv}
universe ua uv upi umon ui
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual
example (g h : ℤ) (c : I.family.index) :
    sourceInd1 I (g + h) c = sourceInd1 I h (sourceInd1 I g c) := by
  unfold sourceInd1
  rw [← Equiv.Perm.mul_apply]
  congr 1
  rw [← zpow_add]
  congr 1
  ring
end Probe
end
