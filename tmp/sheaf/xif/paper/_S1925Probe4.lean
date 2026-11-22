import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open MvPolynomial
open scoped DirectSum
open AlgebraicGeometry

noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] MvPolynomial.gradedAlgebra

namespace S1925ProbeC

variable {R : Type} [CommRing R]

abbrev relIdeal (F : MvPolynomial (Fin 3) R) : Ideal (MvPolynomial (Fin 3) R) := Ideal.span {F}
abbrev Cohom (F : MvPolynomial (Fin 3) R) : Type := MvPolynomial (Fin 3) R ⧸ relIdeal F
abbrev quo (F : MvPolynomial (Fin 3) R) : MvPolynomial (Fin 3) R →ₐ[R] Cohom F :=
  Ideal.Quotient.mkₐ R (relIdeal F)
def CohomGr (F : MvPolynomial (Fin 3) R) (n : ℕ) : Submodule R (Cohom F) :=
  (MvPolynomial.homogeneousSubmodule (Fin 3) R n).map (quo (R := R) F).toLinearMap

variable (F : MvPolynomial (Fin 3) R)

-- what instances are available for the degree-zero part?
example : CommRing (↥(CohomGr F 0)) := inferInstance
example : Algebra (↥(CohomGr F 0)) (Cohom F) := inferInstance
example : Module (↥(CohomGr F 0)) (Cohom F) := inferInstance

-- Proj
def P : Scheme := Proj (CohomGr F)
def tz : P F ⟶ Spec (CommRingCat.of (↥(CohomGr F 0))) := Proj.toSpecZero (CohomGr F)

-- with a local assumption of finite type, do we get IsProper?
example [Algebra.FiniteType (↥(CohomGr F 0)) (Cohom F)] : IsProper (tz F) := inferInstance

#check @AlgebraicGeometry.Proj.instIsProperToSpecZero
#check @AlgebraicGeometry.Proj.toSpecZero
#check @AlgebraicGeometry.Proj.awayι
#check @AlgebraicGeometry.Proj.fromOfGlobalSections
#check @AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen

end S1925ProbeC
