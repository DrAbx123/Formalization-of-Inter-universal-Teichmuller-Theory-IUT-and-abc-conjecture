import tmp.sheaf.xif.paper.S3123FiberEquivalenceOfDataDirectActual
import tmp.sheaf.xif.paper.S3123FiberEquivalenceActual
import tmp.sheaf.xif.paper.S3123StrongTransVcompEqActual

/-! # Stage-4 host: fiber functor host and its exact missing component

Source: IUT III, Theorem 3.11 (multiradial algorithm / fiber functor);
"Formalization of IUT (2026-04)", §4 (:443-621) — BPS -> multiradial
representation fiber; Stage 4 supplies the earlier results.

What is actual here (all kernel-checked, reused from the S3123 chain):
* `S3123Left`, `S3123Right`: the two actual etale-stack pseudofunctors;
* `S3123FiberApp`, `S3123FiberAppInv`: the actual functors induced by the
  `Over.mapPullback` adjunction `Over.mapPullbackAdj`;
* `S3123FiberStrongTrans` / `S3123FiberStrongTransInv`: the two actual strong
  transformations;
* `S3123FiberStrongTrans_vcomp_app`: the composite strong transformation is
  pointwise `S3123FiberApp U ≫ S3123FiberAppInv U` (rfl).

The exact missing object (component layer, not an interface equivalence): the
strong unit/counit isomorphisms `S3123UnitIsoData` / `S3123CounitIsoData` of
`S3123UnitIsoDataActual`.  These are precisely the component data needed by
`S3123FiberEquivalenceOfData` to obtain the actual bicategory equivalence of
the fiber categories.  The existing `Direct` route only restates that
consumption; it does not construct the data.  No weakening is made below. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataDirectActual
open LeanFormal.IUT.XiFPaper.S3123StrongTransVcompEqActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3136FiberHostGapActual

variable {l : PrimeGeFive}

/-- The exact missing Stage-4 fiber-host object, as a Prop: the component-layer
strong unit and counit data for the two actual strong transformations. -/
def S3136FiberHostMissing : Prop :=
  Nonempty (S3123UnitIsoData (l := l)) ∧ Nonempty (S3123CounitIsoData (l := l))

/-- The target bicategory equivalence of the two actual fiber pseudofunctors. -/
def S3136FiberHostTarget : Prop :=
  Nonempty (Bicategory.Equivalence (S3123Result (l := l)).fiber
    (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
      (S1280Arithmetic l).F (S1280Arithmetic l).K)
      (S1536XF (l := l)).stack.fiber))

/-- The actual fiber-host target follows from exactly the missing component
data; this is the honest conditional form (no interface equivalence is being
promoted to a proof). -/
theorem S3136FiberHostTarget_of_data
    (η : S3123UnitIsoData (l := l)) (ε : S3123CounitIsoData (l := l)) :
    S3136FiberHostTarget (l := l) :=
  S3123FiberEquivalenceOfDataDirect_nonempty (l := l) η ε

/-- Pointwise form of the actual composite strong transformation, recorded for
the component-layer construction: it is `S3123FiberApp U ≫ S3123FiberAppInv U`. -/
theorem S3136FiberHostComposite_app
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTrans)
      (S3123FiberStrongTransInv)).app U =
      (S3123FiberApp (l := l) U ≫ S3123FiberAppInv (l := l) U) :=
  S3123FiberStrongTrans_vcomp_app U

/-- The missing component data yields the two strong isomorphisms between
`StrongTrans.id` and the two actual composite strong transformations. -/
theorem S3136FiberHostMissing_unitIso
    (h : S3136FiberHostMissing (l := l)) :
    Nonempty (Pseudofunctor.StrongTrans.id (S3123Result (l := l)).fiber ≅
      Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTrans)
        (S3123FiberStrongTransInv)) ∧
    Nonempty (Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTransInv)
        (S3123FiberStrongTrans) ≅
      Pseudofunctor.StrongTrans.id (S3123Right (l := l))) := by
  obtain ⟨⟨η⟩, ⟨ε⟩⟩ := h
  exact ⟨⟨η.toIso⟩, ⟨ε.toIso⟩⟩

#check S3136FiberHostMissing
#check S3136FiberHostTarget
#check S3136FiberHostTarget_of_data
#check S3136FiberHostComposite_app
#check S3136FiberHostMissing_unitIso

end LeanFormal.IUT.XiFPaper.S3136FiberHostGapActual
end
