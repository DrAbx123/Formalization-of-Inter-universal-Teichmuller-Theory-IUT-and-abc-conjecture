
import tmp.sheaf.xif.paper.S1858GlobalTraceActual
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 20
open scoped TensorProduct
open LinearMap
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual

namespace Probe7

variable (A : CommAlgCat.FiniteEtale.{0} S1779R) (p : Ideal S1779R) [p.IsPrime] [p.IsMaximal]

example : AddCommGroup (Localization.AtPrime p ⊗[S1779R] (A : Type)) := inferInstance
example : CommRing (Localization.AtPrime p ⊗[S1779R] (A : Type)) := inferInstance
example : Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) := inferInstance
example : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) := inferInstance

example : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) := by
  haveI : IsLocalRing (Localization.AtPrime p) := inferInstance
  haveI : Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) := inferInstance
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) := inferInstance
  exact Module.free_of_flat_of_isLocalRing

end Probe7
