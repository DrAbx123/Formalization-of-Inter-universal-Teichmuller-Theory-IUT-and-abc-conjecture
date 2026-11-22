import tmp.sheaf.xif.paper.S3036IsDomainR0
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S3036IsDomainR0
open Polynomial
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3042R0Bridge

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : DecidableEq K := Classical.decEq _

abbrev W : WeierstrassCurve K := S2801E37Curve K

/-- The explicit algebra equivalence from K[x,y] (x = X 0, y = X 1) to
K[X][Y] (outer Y, inner X), sending x to C X and y to Y. -/
noncomputable def S3042E :
    MvPolynomial (Fin 2) K ≃+* Polynomial (Polynomial K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    ((MvPolynomial.finSuccEquiv K 1).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv))

theorem S3042E_X0 : S3042E (MvPolynomial.X (0 : Fin 2)) = Polynomial.C Polynomial.X := by
  show (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)
      ((MvPolynomial.finSuccEquiv K 1)
        ((MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)) (MvPolynomial.X 0))) =
    Polynomial.C Polynomial.X
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)
      ((MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X 1)) = Polynomial.C Polynomial.X
  change (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)
      ((MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X (Fin.succ 0))) =
    Polynomial.C Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.mapEquiv]

theorem S3042E_X1 : S3042E (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
  show (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)
      ((MvPolynomial.finSuccEquiv K 1)
        ((MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)) (MvPolynomial.X 1))) =
    Polynomial.X
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)
      ((MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X 0)) = Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_zero]
  simp [Polynomial.mapEquiv]

theorem S3042E_C (a : K) :
    S3042E (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  show (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)
      ((MvPolynomial.finSuccEquiv K 1)
        ((MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)) (MvPolynomial.C a))) =
    Polynomial.C (Polynomial.C a)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
  simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, Polynomial.mapEquiv]

/-- The bridge polynomial identity: S2801E37Polynomial maps to W.polynomial. -/
theorem S3042E_polynomial :
    S3042E (S2801E37Polynomial K) = W.toAffine.polynomial := by
  simp only [S2801E37Polynomial, S2801E37Curve, weierstrassAffinePolynomial,
    WeierstrassCurve.Affine.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat]
  rw [S3042E_X0, S3042E_X1]
  rw [S3042E_C]
  ring

/-- The R0 bridge: R0 = K[x,y]/(S2801E37Polynomial) is ring-equivalent to
Mathlib's Weierstrass affine coordinate ring AdjoinRoot W.polynomial. -/
noncomputable def S3042R0Bridge :
    S3030AffineOriginClassification.R0 ≃+*
      (W.toAffine.CoordinateRing) := by
  change (MvPolynomial (Fin 2) K ⧸ S2801E37Ideal K) ≃+*
    (Polynomial (Polynomial K) ⧸ Ideal.span {W.toAffine.polynomial})
  exact Ideal.quotientEquiv (S2801E37Ideal K)
    (Ideal.span {W.toAffine.polynomial}) S3042E
    (by
      rw [S2801E37Ideal, Ideal.map_span, Set.image_singleton]
      exact (congrArg (fun x => Ideal.span ({x} : Set (Polynomial (Polynomial K))))
        S3042E_polynomial).symm)

/-- S3036BridgeTarget is actual. -/
theorem S3042_bridgeTarget : S3036BridgeTarget :=
  ⟨S3042R0Bridge⟩

/-- Hence R0 is a domain, actually. -/
theorem S3042_r0_isDomain : IsDomain S3030AffineOriginClassification.R0 :=
  S3036_domain_of_bridge S3042_bridgeTarget

#check S3042E
#check S3042E_X0
#check S3042E_X1
#check S3042E_polynomial
#check S3042R0Bridge
#check S3042_bridgeTarget
#check S3042_r0_isDomain
#print axioms S3042E_polynomial
#print axioms S3042_bridgeTarget
#print axioms S3042_r0_isDomain

end LeanFormal.IUT.XiFPaper.S3042R0Bridge
end
