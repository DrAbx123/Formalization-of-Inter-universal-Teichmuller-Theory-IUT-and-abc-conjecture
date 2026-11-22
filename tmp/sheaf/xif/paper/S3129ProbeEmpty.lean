import tmp.sheaf.xif.paper.S3128PullbackCoproductActual
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
namespace LeanFormal.IUT.XiFPaper.S3129ProbeEmpty
variable {l : PrimeGeFive}
#check Scheme.emptyTo
#check (Scheme.emptyTo (Spec (CommRingCat.of (S1348K l))))
example : IsFinite (Scheme.emptyTo (Spec (CommRingCat.of (S1348K l)))) := inferInstance
example : Etale (Scheme.emptyTo (Spec (CommRingCat.of (S1348K l)))) := inferInstance
example : Unique (Scheme.empty ⟶ (S1419AffineOver l).left) := inferInstance
end LeanFormal.IUT.XiFPaper.S3129ProbeEmpty
end