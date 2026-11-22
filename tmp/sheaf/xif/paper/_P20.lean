import tmp.sheaf.xif.paper.S1898EllipticInvolutionActual
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# S1932: the coherent sign action on the actual S1726 orbicurve

S1898 constructed the actual `[-1]` endomorphism `S1898EllipticInvolution` of
the S1726 orbicurve stack and proved it nonidentity.  The first missing field
of `S1886PaperCF` was the coherent sign-action packaging
`Iut.OrbicurveSignAction S1726Orbicurve`, whose `inversion` is that actual
endomorphism.

This file constructs it.  The two ingredients are:

* `S1932SigmaSqIso : (Sigma ; Sigma) ~= 1`, the square of the actual
  endomorphism is the identity, obtained from the actual scheme-level
  involution `[-1] ; [-1] = id` on the affine Weierstrass model
  (a coordinate-ring computation, not a postulate);
* `S1932Diagram : SignActionIndex ~> EtaleStackPseudofunctor F'`, the
  pseudofunctor whose value on the generator is `Sigma` and whose
  coherence 2-cells are the unitors and the square iso.

All 2-cells between endomorphisms of the representable S1726 stack live in
the discrete category `Discrete (U.unop -> Spec R')`; hence they are
subsingletons, which is what lets the pseudofunctor coherence equations be
discharged.  The base equivalence is the identity equivalence, so the
`generator_identification` field is a unitor computation.

## What remains after this file

The quotient `C_F = X_F/{+-1}` of paper type (1,1)^pm: an actual orbicurve
with a sign-invariant quotient morphism and the bicategorical universal
property.  This file isolates it exactly (`S1932CFQuotient`) and proves that
it, together with the action constructed here, yields `S1886PaperCF`.
Nothing is assumed about the quotient.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

/-! ## 1. 2-cells between endomorphisms of the representable stack -/

/-- Natural transformations between functors into a discrete category are
subsingletons. -/
theorem S1932NatTransSubsingleton {X Y : Cat.{0, 0}} (hY : IsDiscrete (Y : Type))
    (F G : X ⟶ Y) : Subsingleton (F ⟶ G) := by
  letI := hY
  constructor
  intro α β
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-- 2-cells in `Cat` between endomorphisms of the representable S1726 stack are
subsingletons. -/
theorem S1932CatHom₂Subsingleton (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (F G : S1898Stack.obj U ⟶ S1898Stack.obj U) : Subsingleton (F ⟶ G) :=
  S1932NatTransSubsingleton (Discrete.isDiscrete _) F G

/-- Modifications between endomorphisms of the actual S1726 stack are
subsingletons: every component lands in a discrete category. -/
theorem S1932StrongTransSubsingleton
    (F G : Pseudofunctor.StrongTrans S1898Stack S1898Stack) : Subsingleton (F ⟶ G) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S1932CatHom₂Subsingleton U (F.app U) (G.app U)).elim _ _

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
