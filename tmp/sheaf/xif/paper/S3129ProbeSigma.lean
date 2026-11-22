import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3129ProbeSigma
example : IsZariskiLocalAtSource @Etale := inferInstance
example : IsZariskiLocalAtSource @IsFinite := inferInstance
example {ι : Type} [Small.{0} ι] {X : Scheme.{0}} {Y : ι -> Scheme.{0}}
  (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i)] : Etale (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun i => inferInstance)
end LeanFormal.IUT.XiFPaper.S3129ProbeSigma
end