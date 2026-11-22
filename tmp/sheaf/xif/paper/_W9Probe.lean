import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open groupCohomology
open CategoryTheory

variable {G M : Type} [Group G] [CommGroup M]

example : Module ℤ (Additive M) := inferInstance

example : (Rep.trivial ℤ G (Additive M)).IsTrivial := inferInstance

example (φ : G →* M) : Additive G →+ Additive M :=
  (MonoidHom.toAdditive φ)

example (φ : G →* M) (x : Additive G) :
    (MonoidHom.toAdditive φ) x = Additive.ofMul (φ x.toMul) := rfl

