import Mathlib
open WeierstrassCurve
noncomputable section
namespace Probe1558
variable {L : Type*} [Field L] (W : WeierstrassCurve L)
#synth Add (WeierstrassCurve.Affine.Point W)
#synth AddCommGroup (WeierstrassCurve.Affine.Point W)
#check (inferInstance : Add (WeierstrassCurve.Affine.Point W))
example : Add (WeierstrassCurve.Affine.Point W) := inferInstance
end Probe1558
