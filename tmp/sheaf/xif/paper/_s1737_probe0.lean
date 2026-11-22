/-
Probe for S1737: Mathlib-native fundamental group statements.
-/
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Iut.Foundations.SourceContinuousAnabelioid
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1737Probe

variable (G : ProfiniteGrp.{0}) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The already-proved continuous-action fundamental-group theorem, restated. -/
example : PreGaloisCategory.IsFundamentalGroup (Iut.continuousActionFiber G) G :=
  Iut.continuousAction_isFundamentalGroup G

/-- The literal full-action statement typechecks (with the scoped discrete topology). -/
example : Prop :=
  PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G

/-- The naturality instance for the full forgetful functor. -/
example : PreGaloisCategory.IsNaturalSMul (Action.forget FintypeCat.{0} G) G := by
  infer_instance

end S1737Probe
