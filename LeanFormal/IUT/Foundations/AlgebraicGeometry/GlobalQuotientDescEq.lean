import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: scheme-level desc equations

This file records the exact scheme-level equations satisfied by the desc
morphism of the global glued quotient.  All equations are consequences of the
production desc/glue interface; no new construction or provider is introduced.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescEq

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

namespace GlobalGluedQuotientData

variable (D : GlobalGluedQuotientData S)

/-- The structure map of the glued quotient is the desc morphism of the local
quotient chart maps. -/
theorem structureMap_eq_desc_q :
    D.structureMap = D.desc S D.P.q D.hq :=
  rfl

/-- The desc morphism for the chart family `q` is the glued structure map. -/
theorem desc_q_eq_structureMap :
    D.desc S D.P.q D.hq = D.structureMap :=
  rfl

/-- Restriction of the glued structure map to each local quotient chart. -/
theorem structureMap_restrict_chart (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.structureMap = D.P.q i :=
  D.P.gluedMapOfCompatible_ι D.hq i

/-- The desc morphism is exactly the production glued morphism. -/
theorem desc_eq_ofCompatible (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    D.desc Z f hf = D.P.descOfCompatible Z f hf :=
  rfl

/-- The desc morphism is determined by its values on the local charts: two
compatible families with pointwise equal chart maps give equal desc morphisms. -/
theorem desc_eq_of_chart_family_eq (Z : Scheme.{u})
    (f f' : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (hf' : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f' i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f' j)
    (h : ∀ i : D.P.J, f i = f' i) :
    D.desc Z f hf = D.desc Z f' hf' :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData.desc_congr D Z f f' hf hf' h

/-- The desc morphism for the chart family `q` restricts to `q` on every chart. -/
theorem desc_q_restrict (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc S D.P.q D.hq = D.P.q i :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData.desc_ι D S D.P.q D.hq i

/-- Associativity form of the chart restriction equation for an arbitrary
compatible family. -/
theorem desc_chart_assoc (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j)
    (i : D.P.J) :
    (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf = f i :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData.desc_ι D Z f hf i

/-- The desc morphism is a section of the chart-restriction operation on
compatible families. -/
theorem desc_restrict_eq_self (Z : Scheme.{u})
    (f : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hf : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ f j) :
    (fun i => (D.P.toSchemeGlueData).ι i ≫ D.desc Z f hf) = f :=
  funext (fun i => LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac.GlobalGluedQuotientData.desc_ι D Z f hf i)

end GlobalGluedQuotientData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescEq
end