import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeActual
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.LimitsOver
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2ConstantGroupActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

/-- The constant group scheme Z/2 over `Spec F`, realized as
`Spec (F × F)` with the diagonal structure map. -/
noncomputable def S3128ZMod2ConstantGroup : SchemeOverField F :=
  Over.mk
    (Scheme.Spec.map
      ((CommRingCat.ofHom (algebraMap F (F × F))).op))

/-- The chosen nontrivial generator of the constant Z/2. -/
abbrev S3128ZMod2Generator : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (1 : ZMod 2)

variable (A : S3128ZMod2FiberObj (F := F) X U)

/-- The `(p,p)` component of the torsor map. -/
noncomputable def S3128TorsorMapZero :
    A.P ⟶ pullback A.proj A.proj :=
  pullback.lift (𝟙 A.P) (𝟙 A.P)
    (by simp)

/-- The `(g•p,p)` component of the torsor map. -/
noncomputable def S3128TorsorMapOne :
    A.P ⟶ pullback A.proj A.proj :=
  pullback.lift
    (S3128BaseChangeAutHom A S3128ZMod2Generator)
    (𝟙 A.P)
    (by
      rw [Category.id_comp]
      exact A.action_proj S3128ZMod2Generator)

/-- The torsion/torsor comparison `P ⊔ P → P ×_U P`. -/
noncomputable def S3128TorsorMap :
    (A.P ⨿ A.P) ⟶ pullback A.proj A.proj :=
  coprod.desc (S3128TorsorMapZero A) (S3128TorsorMapOne A)

/-- Target: the comparison is an isomorphism (free and transitive Z/2-torsor). -/
def S3128TorsorIsoTarget : Prop :=
  IsIso (S3128TorsorMap A)

#check S3128ZMod2ConstantGroup
#check S3128TorsorMapZero
#check S3128TorsorMapOne
#check S3128TorsorMap
#check S3128TorsorIsoTarget

end LeanFormal.IUT.XiFPaper.S3128ZMod2ConstantGroupActual