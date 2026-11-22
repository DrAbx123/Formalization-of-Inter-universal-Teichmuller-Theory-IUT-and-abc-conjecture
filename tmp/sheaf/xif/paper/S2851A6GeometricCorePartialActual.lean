import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceEtaleStackInstanceSupplyReduction
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT CategoryTheory
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2851A6GeometricCorePartialActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Constructible xF: the hyperbolic orbicurve realized from the point stack
fiber, with the once-punctured elliptic signature. -/
noncomputable def S2851A6XF : Iut.HyperbolicOrbicurve S2847F6 :=
  realizedHyperbolicOrbicurve
    S2847F6
    (LeanFormal.IUT.sourceStackPointEtaleFiber S2847F6)
    (LeanFormal.IUT.sourceStackPointEtaleFiber_isStack S2847F6)
    sourceTypeOneOne
    sourceTypeOneOne_hyperbolic

/-- Constructible xF_geometry: the once-punctured-elliptic geometry of xF. -/
noncomputable def S2851A6XFGeometry :
    SourceOncePuncturedGeometry S2847A6.curve S2851A6XF :=
  ⟨by
    show (realizedHyperbolicOrbicurve S2847F6 (sourceStackPointEtaleFiber S2847F6)
      (sourceStackPointEtaleFiber_isStack S2847F6) sourceTypeOneOne
      sourceTypeOneOne_hyperbolic).signature = sourceTypeOneOne
    exact realizedHyperbolicOrbicurve_signature S2847F6
      (sourceStackPointEtaleFiber S2847F6)
      (sourceStackPointEtaleFiber_isStack S2847F6) sourceTypeOneOne
      sourceTypeOneOne_hyperbolic⟩

/-- Constructible elliptic involution: the identity morphism on xF. -/
noncomputable def S2851A6Involution :
    S2851A6XF.Hom S2851A6XF :=
  Iut.HyperbolicOrbicurve.Hom.id S2851A6XF

/-- Constructible square: the identity involution squares to the identity. -/
noncomputable def S2851A6InvolutionSquared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp S2851A6Involution S2851A6Involution)
      (Iut.HyperbolicOrbicurve.Hom.id S2851A6XF) :=
  Iso.refl _

/-- The 22-field geometric core, with the constructible prefix filled and the
remaining fields (unique involution, sign/quotient, groups, K-side, cusp) as
explicit inputs. -/
structure S2851A6GeometricCorePartial
    (unique_elliptic_involution :
      ∀ inv : S2851A6XF.Hom S2851A6XF,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id S2851A6XF) →
        inv = S2851A6Involution) where
  xF := S2851A6XF
  xF_geometry := S2851A6XFGeometry
  ellipticInvolution := S2851A6Involution
  ellipticInvolution_squared := S2851A6InvolutionSquared
  unique_elliptic_involution := unique_elliptic_involution

#check S2851A6XF
#check S2851A6XFGeometry
#check S2851A6Involution
#check S2851A6InvolutionSquared
#check S2851A6GeometricCorePartial

end LeanFormal.IUT.XiFPaper.S2851A6GeometricCorePartialActual
end
