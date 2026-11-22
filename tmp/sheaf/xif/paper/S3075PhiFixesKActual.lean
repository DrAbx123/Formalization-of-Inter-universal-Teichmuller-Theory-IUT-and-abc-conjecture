import tmp.sheaf.xif.paper.S3074PhiFixesKActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import Mathlib.Algebra.MvPolynomial.Basic
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3074PhiFixesKActual
open LeanFormal.IUT.XiFPaper.S3073ChartZRestrictionActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3075PhiFixesKActual
abbrev K0 := LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual.K
abbrev R0 := LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37CoordinateRing K0
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field K0 := S2847A6.fieldF
local instance : NumberField K0 := S2847A6.numberFieldF
local instance : DecidableEq K0 := Classical.decEq _
local instance : CommRing R0 := Ideal.Quotient.commRing (LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37Ideal K0)
local instance : Algebra K0 R0 := RingHom.toAlgebra ((Ideal.Quotient.mk (LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual.S2801E37Ideal K0)).comp (MvPolynomial.C : K0 →+* MvPolynomial (Fin 2) K0))
theorem S3075_phi_fixes_K
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β)
    (D : S3073ChartZRestriction β) :
    ∀ a : K0, D.φ.toRingHom (algebraMap K0 R0 a) = algebraMap K0 R0 a := by
  intro a
  have hzover := S3074_zOver β hβ hfix D
  rw [D.hz] at hzover
  change Spec.map (CommRingCat.ofHom D.φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K0 R0)) = Spec.map (CommRingCat.ofHom (algebraMap K0 R0)) at hzover
  rw [← Spec.map_comp] at hzover
  have hring := Spec.map_injective hzover
  have hval := congrArg (fun f => f.hom a) hring
  exact hval
#check S3075_phi_fixes_K
#print axioms S3075_phi_fixes_K
end LeanFormal.IUT.XiFPaper.S3075PhiFixesKActual
end
