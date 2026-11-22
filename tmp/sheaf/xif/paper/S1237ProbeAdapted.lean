import tmp.sheaf.xif.paper.S1231SourceCoreActual
noncomputable section
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
namespace Probe
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual
example : sourceInd3 I 1 (I.indexOf 0 0) = I.indexOf 1 0 := by
  simp [sourceInd3, translatePerm, I.translate_theater]
example : sourceInd1 I (-1) (I.indexOf 0 0) = I.indexOf 1 0 := by
  simp [sourceInd1, horizontalPerm, I.horizontal_shift_theater]
end Probe
end
