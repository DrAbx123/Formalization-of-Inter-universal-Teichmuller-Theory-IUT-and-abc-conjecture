import tmp.sheaf.xif.paper.S1829FiberCoveredYonedaActual

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1829ProbeIso

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1829FiberCoveredYonedaActual
open LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

variable (cover : S1735Cover) (x : S1735Fiber cover)

example : IsIso (S1829SectionMorphism cover x) := by
  infer_instance

end LeanFormal.IUT.XiFPaper.S1829ProbeIso
