import tmp.sheaf.xif.paper.S2029GiraudStackificationActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import tmp.sheaf.xif.paper.S1983EtThSignatureBridgeActual
import tmp.sheaf.xif.paper.S1994KSideCoversActual

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2050D9UniverseChoiceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1994KSideCovers

universe u

/-! ## 1. The two universe targets -/

/-- The old target: category-valued etale stacks with Cat.{u,u} fibres. -/
abbrev S2050OldEtaleStackPseudofunctor (K : Type u) [Field K] :=
  Iut.EtaleStackPseudofunctor K

/-- The proposed universe-corrected target: Cat.{u+1,u+1}-valued pseudofunctors
on the same etale site. This is the universe in which the natural slice-sheaf /
torsor models live. -/
abbrev S2050LargeEtaleStackPseudofunctor (K : Type u) [Field K] :=
  Pseudofunctor (LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) Cat.{u+1, u+1}

/-- A universe-corrected category-valued etale stack. -/
structure S2050LargeEtaleStackOverField (K : Type u) [Field K] where
  fiber : S2050LargeEtaleStackPseudofunctor K
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology K)

/-- The available universe choices, as an explicit finite tag. This is a
target-choice record, not a proof of either route. -/
inductive S2050UniverseRoute
  | keepSmallTarget
  | raiseToLargeTarget
  deriving DecidableEq, Repr

/-! ## 2. The actual large-valued natural model -/

/-- The actual slice-sheaf pseudofunctor in Cat.{u+1,u+1}. This is an actual
object, not a quotient-stack construction. -/
noncomputable def S2050LargeSheafPrestack (K : Type u) [Field K] :
    S2050LargeEtaleStackPseudofunctor K :=
  S2029SheafPrestack K

/-- Its value at a test object is the actual slice-sheaf category. -/
theorem s2050LargeSheafPrestack_obj (K : Type u) [Field K]
    (U : Iut.SchemeOverField K) :
    (S2050LargeSheafPrestack K).obj (LocallyDiscrete.mk (Opposite.op U)) =
      S2029SliceSheafCategory K U :=
  S2029SheafPrestack_obj K U

/-- The concrete large-universe stack-of-sheaves first missing. -/
def S2050LargeSheafStackMissing (K : Type u) [Field K] : Prop :=
  (S2050LargeSheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K)

/-- The large-universe small-model input for the natural sheaf model: every
slice-sheaf value admits a u-small model. -/
def S2050LargeSheafSmallModel (K : Type u) [Field K] : Prop :=
  Nonempty (forall U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
    S2029SmallModel ((S2050LargeSheafPrestack K).obj U))

/-! ## 3. Target-change proposal and exact first missing -/

/-! ## 3b. Actual large-universe C_F target data -/

/-- A C_F quotient in the universe-corrected target: an actual large etale
stack over F, the quotient orbicurve, the sign-invariant quotient morphism, the
bicategorical witness, and the honest signature.  No inhabitant is asserted. -/
structure S2050LargeCFData (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) where
  stack : S2050LargeEtaleStackOverField (S1732A l).F
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient
  honest_signature : cF.signature = S1964HonestQuotientSignature

/-- The large-universe C_F exact first missing. -/
def S2050LargeCFFirstMissing (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  Nonempty (S2050LargeCFData l A)

/-- Actual consumer: large-universe C_F data gives the S1964 quotient
structure. -/
def s2050LargeCF_toS1964 {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (D : S2050LargeCFData l A) : S1964QuotientStructure l A :=
  ⟨D.cF, D.quotient, D.quotientWitness⟩

/-- The old C_F quotient-stack target remains the F-side first missing if the
target is not changed. -/
def S2050CFFirstMissing : Prop :=
  S1971QuotientStack

/-- The K-side geometric first missing remains an actual stacky K-side
orbicurve. -/
def S2050KSideFirstMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l) : Prop :=
  S1994StackyOrbicurveMissing l A

/-- The actual honest signature is not the old (1,1)^pm label. -/
theorem s2050HonestSignature_actual :
    etthSignature paperCFType = S1964HonestQuotientSignature :=
  paperCF_signature

#print axioms s2050LargeSheafPrestack_obj
#print axioms s2050HonestSignature_actual

end LeanFormal.IUT.XiFPaper.S2050D9UniverseChoiceActual

end
