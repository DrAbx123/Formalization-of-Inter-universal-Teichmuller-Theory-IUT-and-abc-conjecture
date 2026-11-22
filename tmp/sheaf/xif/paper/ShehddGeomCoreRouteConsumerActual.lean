import tmp.sheaf.xif.paper.Mzk1GeomCoreFiniteMapRouteActual

/-!
# ShehddGeomCoreRouteConsumerActual — combined precise-witness + recast consumer

STEP 0 prior-art (reuse only): Mzk1GeomCoreFiniteMapRouteActual provides
* preciseWitness_of_route: Mzk1FiniteMapData + bridge + positive degree + generic
  etaleness + pullback degree => Mzk1GeometricCoreWitnessPreciseRestated;
* recast_of_route: same inputs => Mzk1GeometricCoreRecast.

This file composes the two PROVED route consumers into one theorem exposing both
conclusions from the same hypotheses (finite-map route -> precise witness + old recast).
No new assumptions, no sorry/axiom; the finite-map construction itself stays NAMED
(see Mzk1GeomCoreFiniteMapRouteActual finiteMapRouteGapText).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddGeomCoreRouteConsumerActual

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeLegacyActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapRouteActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- **PROVED composition:** a finite-map datum together with the bridge, positive degree,
generic etaleness and pullback degree yields BOTH the legacy restated precise witness and
the old recast, in one theorem. -/
theorem route_precise_and_recast {F : Type*} [Field F] {P : Type*} (ord : P → F → ℤ)
    (fm : Mzk1FiniteMapData c ε) (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
        (B.placePoint '' (B.Tplaces : Set P)) D ∧
      Mzk1GeometricCoreRecast c ε (B.placePoint '' (B.Tplaces : Set P)) D :=
  ⟨preciseWitness_of_route ord fm hdeg B D hunram hpull,
    recast_of_route ord fm hdeg B D hunram hpull⟩

/-- Row record: reused route consumers vs the composed theorem. -/
def geomCoreRouteConsumerRows : List (String × String × String) :=
  [ ("fine map datum + bridge => precise witness", "REUSED PROVED", "Mzk1GeomCoreFiniteMapRouteActual.preciseWitness_of_route")
  , ("fine map datum + bridge => old recast", "REUSED PROVED", "Mzk1GeomCoreFiniteMapRouteActual.recast_of_route")
  , ("both conclusions in one consumer", "COMPOSED PROVED", "route_precise_and_recast")
  , ("finite-map construction / line-bundle iso", "NAMED", "Mzk1GeomCoreFiniteMapRouteActual.finiteMapRouteGapText (exact gaps)") ]

theorem geomCoreRouteConsumerRows_length : geomCoreRouteConsumerRows.length = 4 := rfl

#check route_precise_and_recast
#check geomCoreRouteConsumerRows_length

end LeanFormal.IUT.XiFPaper.ShehddGeomCoreRouteConsumerActual
end
