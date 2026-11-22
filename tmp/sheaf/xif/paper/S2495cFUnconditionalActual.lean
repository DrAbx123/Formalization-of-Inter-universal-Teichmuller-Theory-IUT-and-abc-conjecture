import tmp.sheaf.xif.paper.S2494cFGeometryActual
import tmp.sheaf.xif.paper.S2199RepresentableStackActual
import tmp.sheaf.xif.paper.S2463InvariantQuotientActual
import Mathlib.RingTheory.MvPolynomial.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual
open LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2463InvariantQuotientActual
open LeanFormal.IUT.XiFPaper.S2494cFGeometryActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual

/-- Actual `EtaleStackInstanceSupply` from a representable scheme: the
representable pseudofunctor is an etale stack (S2199). -/
theorem S2495StackSupply
    (F : Type) [Field F] (X : Iut.SchemeOverField F) :
    EtaleStackInstanceSupply F :=
  ⟨Iut.schemeRepresentableEtalePseudofunctor F X,
   s2199_representable_isStack F X⟩

/-- The affine `Spec F[x]` object over `F` used for `cF`. -/
abbrev S2495FOver : Iut.SchemeOverField S2490A.F := S2463cFOver

/-- The affine `Spec K[x]` object over `K` used for `cK`. -/
noncomputable def S2495KOver : Iut.SchemeOverField S2490A.K :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap S2490A.K (MvPolynomial (Fin 1) S2490A.K))))

/-- Unconditional actual `cF` over `Q(i)` as the representable etale stack of
`Spec F[x]`, with the source type-one plus-minus signature. -/
noncomputable def S2495cF : Iut.HyperbolicOrbicurve S2490A.F :=
  S2494cF
    (Iut.schemeRepresentableEtalePseudofunctor S2490A.F S2495FOver)
    (s2199_representable_isStack S2490A.F S2495FOver)

theorem S2495cF_signature :
    S2495cF.signature = sourceTypeOneLTorsionPlusMinus S2482Arithmetic.l5 :=
  S2494cF_signature _ _

/-- Unconditional actual `cK` over `Q(i)` as the representable etale stack of
`Spec K[x]`, with the same source signature. -/
noncomputable def S2495cK : Iut.HyperbolicOrbicurve S2490A.K :=
  S2494cK
    (Iut.schemeRepresentableEtalePseudofunctor S2490A.K S2495KOver)
    (s2199_representable_isStack S2490A.K S2495KOver)

theorem S2495cK_signature :
    S2495cK.signature = sourceTypeOneLTorsionPlusMinus S2482Arithmetic.l5 :=
  S2494cK_signature _ _

theorem S2495_cFStackSupply : S2494StackSupply S2490A.F :=
  S2495StackSupply S2490A.F S2495FOver

theorem S2495_cKStackSupply : S2494StackSupply S2490A.K :=
  S2495StackSupply S2490A.K S2495KOver

#print axioms S2495cF_signature
#print axioms S2495cK_signature

end LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
end