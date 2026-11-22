import tmp.sheaf.xif.paper.S2463InvariantQuotientActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import tmp.sheaf.xif.paper.S2490RestrictionSectionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2463InvariantQuotientActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2494cFGeometryActual

universe u

/-- The geometric core needed to realize `cF`: one etale stack fiber over
`S2490A.F` with effective descent.  This is exactly the missing unit recorded
by `S2463cFHyperbolicMissing`; the affine `Spec F[x]` model alone does not
produce a stack. -/
def S2494StackSupply (F : Type u) [Field F] : Prop :=
  EtaleStackInstanceSupply F

theorem S2494_stackSupply_iff_nonempty_hyperbolic (F : Type u) [Field F] :
    S2494StackSupply F ↔ Nonempty (Iut.HyperbolicOrbicurve F) :=
  ⟨fun h => (nonempty_hyperbolicOrbicurve_iff_stackInstanceSupply F).mpr h,
   fun h => (nonempty_hyperbolicOrbicurve_iff_stackInstanceSupply F).mp h⟩

/-- Conditional actual construction of `cF` with the source type-one
plus-minus signature from a supplied etale stack fiber. -/
noncomputable def S2494cF
    (fiber : Iut.EtaleStackPseudofunctor S2490A.F)
    (isStack : CategoryTheory.Pseudofunctor.IsStack fiber (Iut.SchemeOverField.etaleTopology S2490A.F)) :
    Iut.HyperbolicOrbicurve S2490A.F :=
  realizedHyperbolicOrbicurve S2490A.F fiber isStack
    (sourceTypeOneLTorsionPlusMinus S2482Arithmetic.l5)
    (sourceTypeOneLTorsionPlusMinus_hyperbolic S2482Arithmetic.l5)

theorem S2494cF_signature
    (fiber : Iut.EtaleStackPseudofunctor S2490A.F)
    (isStack : CategoryTheory.Pseudofunctor.IsStack fiber (Iut.SchemeOverField.etaleTopology S2490A.F)) :
    (S2494cF fiber isStack).signature = sourceTypeOneLTorsionPlusMinus S2482Arithmetic.l5 :=
  realizedHyperbolicOrbicurve_signature S2490A.F fiber isStack _ _

/-- The affine `Spec F[x]` model of S2463 realizes the hyperbolic orbicurve
`cF` exactly when one etale stack fiber is supplied. -/
theorem S2494_cFHyperbolicMissing_iff_stackSupply :
    S2463cFHyperbolicMissing S2482Arithmetic.l5 ↔ S2494StackSupply S2490A.F := by
  constructor
  · rintro ⟨cF, hsig⟩
    exact (nonempty_hyperbolicOrbicurve_iff_stackInstanceSupply S2490A.F).mp ⟨cF⟩
  · intro hsupply
    obtain ⟨fiber, hstack⟩ := hsupply
    exact ⟨S2494cF fiber hstack, S2494cF_signature fiber hstack⟩

/-- Conditional actual construction of `cK` over `K = Q(i)`.  There is no
base-change API on `Iut.HyperbolicOrbicurve` in the tree, so `cK` is built from
its own supplied stack fiber; identifying it with the base change of `cF`
remains the precise missing geometric unit. -/
noncomputable def S2494cK
    (fiber : Iut.EtaleStackPseudofunctor S2490A.K)
    (isStack : CategoryTheory.Pseudofunctor.IsStack fiber (Iut.SchemeOverField.etaleTopology S2490A.K)) :
    Iut.HyperbolicOrbicurve S2490A.K :=
  realizedHyperbolicOrbicurve S2490A.K fiber isStack
    (sourceTypeOneLTorsionPlusMinus S2482Arithmetic.l5)
    (sourceTypeOneLTorsionPlusMinus_hyperbolic S2482Arithmetic.l5)

theorem S2494cK_signature
    (fiber : Iut.EtaleStackPseudofunctor S2490A.K)
    (isStack : CategoryTheory.Pseudofunctor.IsStack fiber (Iut.SchemeOverField.etaleTopology S2490A.K)) :
    (S2494cK fiber isStack).signature = sourceTypeOneLTorsionPlusMinus S2482Arithmetic.l5 :=
  realizedHyperbolicOrbicurve_signature S2490A.K fiber isStack _ _

theorem S2494_cK_nonempty_iff_stackSupply :
    Nonempty (Iut.HyperbolicOrbicurve S2490A.K) ↔ S2494StackSupply S2490A.K :=
  (S2494_stackSupply_iff_nonempty_hyperbolic S2490A.K).symm

#print axioms S2494_cFHyperbolicMissing_iff_stackSupply
#print axioms S2494cF_signature
#print axioms S2494cK_signature

end LeanFormal.IUT.XiFPaper.S2494cFGeometryActual
end