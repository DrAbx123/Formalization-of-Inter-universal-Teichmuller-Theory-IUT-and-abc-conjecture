import tmp.sheaf.xif.paper.S3128OverForgetPreservesActual
import Mathlib.CategoryTheory.Extensive
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128OverForgetPreservesActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128SchemeCoproductBaseChangeActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

/-- Scheme-level source object of the distribution iso:
`(∐_{Bool} P.left) ×_{U.left} (∐_{Unit} U'.left)`. -/
abbrev S3128SchemeDistributionPullback : Scheme :=
  pullback
    (Sigma.desc (fun _ : Bool => Over.Hom.left A.proj))
    (Sigma.desc (fun _ : Unit => Over.Hom.left f))

/-- Scheme-level target: the coproduct of the two underlying pullbacks. -/
abbrev S3128SchemeDistributionCoproduct : Scheme :=
  ∐ (fun _ : Bool × Unit =>
    pullback (Over.Hom.left A.proj) (Over.Hom.left f))

/-- Scheme-level distribution iso from `FinitaryPreExtensive.isIso_sigmaDesc_map`. -/
noncomputable def S3128SchemeCoproductBaseChangeIso :
    S3128SchemeDistributionPullback f A ≅
      S3128SchemeDistributionCoproduct f A := by
  let φ : S3128SchemeDistributionCoproduct f A ⟶
      S3128SchemeDistributionPullback f A :=
    Sigma.desc fun p : Bool × Unit =>
      pullback.map
        (Over.Hom.left A.proj) (Over.Hom.left f)
        (Sigma.desc fun _ : Bool => Over.Hom.left A.proj)
        (Sigma.desc fun _ : Unit => Over.Hom.left f)
        (Sigma.ι (fun _ : Bool => Over.left A.P) p.1)
        (Sigma.ι (fun _ : Unit => Over.left U') p.2)
        (𝟙 (Over.left U))
        (by simp [Sigma.ι_desc]) (by simp [Sigma.ι_desc])
  have hφ : IsIso φ :=
    FinitaryPreExtensive.isIso_sigmaDesc_map
      (C := Scheme)
      (ι := Bool) (ι' := Unit)
      (S := Over.left U)
      (X := fun _ : Bool => Over.left A.P)
      (Y := fun _ : Unit => Over.left U')
      (f := fun _ => Over.Hom.left A.proj)
      (g := fun _ => Over.Hom.left f)
  exact (asIso φ).symm

#check S3128SchemeCoproductBaseChangeIso
#print axioms S3128SchemeCoproductBaseChangeIso

end LeanFormal.IUT.XiFPaper.S3128SchemeCoproductBaseChangeActual