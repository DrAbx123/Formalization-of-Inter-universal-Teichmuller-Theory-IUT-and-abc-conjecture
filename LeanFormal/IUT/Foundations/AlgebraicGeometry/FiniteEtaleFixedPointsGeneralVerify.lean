import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import Mathlib.Tactic

/-!
# Verification for general fixed points and affine general quotient/G2 scope

The fixed-point consumer exposes only the permitted arbitrary-base finite-etale
hypotheses.  The affine consumer is checked to be conditional on an affine
finite etale A/R and a finite G-action; it is not a global scheme quotient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace ABCBridge.FiniteEtaleFixedPointsGeneralVerify

universe u

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

example :
    Algebra.Etale R (fixedPointSubalgebra R A G) ∧
      Module.Finite R (fixedPointSubalgebra R A G) := by
  classical
  exact FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale

variable [DecidableEq G]

example : FiniteEtaleCover (baseSpec (R := R)) := by
  classical
  exact affineQuotientCoverGeneral (R := R) A G

example :
    affineCover (R := R) A inferInstance inferInstance ⟶
      affineQuotientCoverGeneral (R := R) A G := by
  classical
  exact affineQuotientCoverMapGeneral (R := R) A G

end ABCBridge.FiniteEtaleFixedPointsGeneralVerify

#print axioms FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
#print axioms LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer.affineQuotientCoverGeneral
#print axioms LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer.affineQuotientCoverMapGeneral
#print axioms LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer.affineQuotientCover_liftGeneral
#print axioms LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer.affineQuotientCoverLiftGeneral
#print axioms LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer.affineQuotientCoverLiftGeneral_fac
