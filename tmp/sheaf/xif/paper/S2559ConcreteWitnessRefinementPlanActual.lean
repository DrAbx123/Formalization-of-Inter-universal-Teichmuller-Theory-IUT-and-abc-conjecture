/-
# S2559: minimal refinement plan for X.finiteEtale.baseChange

Minimal non-breaking route: do NOT add fields to `EtaleStackFiniteEtaleMorphism`
or `OrbicurveFiniteEtaleCover` (they have hundreds of construction sites).
Instead add a predicate `S2559HasLiftUnique` on the existing finite-etale
structure, prove it for the concrete S2512/S2514 witnesses, and pass it as an
explicit hypothesis to the extraction/EssSurj consumers.
-/
import tmp.sheaf.xif.paper.S2558ConcreteWitnessPlanActual
import tmp.sheaf.xif.paper.S2514IdentityFiniteEtaleActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual

universe u
variable {F : Type u} [Field F]
variable {source target : Iut.EtaleStackOverField F}
variable {map : source.Hom target}

/-- Predicate: every base-change witness of the finite-etale structure has
lift uniqueness.  This is the minimal added coherence, stated without touching
the core structures. -/
def S2559HasLiftUnique
    (hf : Iut.EtaleStackFiniteEtaleMorphism map) : Prop :=
  ∀ (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T) target.fiber),
    let P := hf.baseChange T q
    let sq := Iut.EtalePseudofunctorSquare.mk
      P.toSource P.projectionMap.transformation map q P.commutes
    S2558LiftUnique sq P.isPullback

/-! ## Minimal refinement checklist

1. Core structures `EtaleStackFiniteEtaleMorphism` /
   `OrbicurveFiniteEtaleCover`: unchanged.
2. New predicate `S2559HasLiftUnique` (this file).
3. Prove it for concrete witnesses:
   - S2514IdentityFiniteEtaleActual: witness `S2514IdWitness`, lift = cone.toY;
   - S2512StackOpenImmersionUB: witness `S2512Witness`, lift = pointwise pullback;
   - optional: S1911Witness (same pointwise pullback pattern).
4. Add hypothesis `hLU : S2559HasLiftUnique X.finiteEtale` to:
   - S2555ExtractionIso / S2555CanonicalData_of_extractionIso
   - S2554CanonicalEssSurj
   - S2553CorrectedEssSurj / S2541EssSurjOnRepresentable
5. Consumers of the conditional result:
   - S2549/S2552 unconditional equivalences.

### Why this is minimal
- No core structure field is added: 1019 references to
  `OrbicurveFiniteEtaleCover` and 59 `TwoPullbackWitness` literals stay valid.
- The only new obligation is the explicit `S2559HasLiftUnique` hypothesis at
  the extraction/EssSurj boundary, which can be discharged for concrete
  witnesses without changing the cover category.
- `X.finiteEtale.baseChange` for an arbitrary cover remains abstract; this is
  precisely why the hypothesis cannot be dropped globally.
-/

#check S2559HasLiftUnique
end LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
end