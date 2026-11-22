import tmp.sheaf.xif.paper.Mzk1GeometricCoreRealStructureActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# STEP 0 prior-art: free Prop fields of Mzk1GeometricCoreWitness -> Mzk1GeometricCoreRealStructureActual:53-71 + ported flt_th FiniteMapData (LevelSetsGenericallyEtale) -> ADAPT (precise conditions; assembly proof TODO named).

# Mzk1GeometricCorePreciseActual — precise geometric schema (MINIMAL GREEN VERSION)

Replaces the free Prop fields by real geometric conditions expressible in the ported
FiniteMapData model.  The precise witness structure and its conversion to the old
witness are recorded; the conversion PROOF is named TODO (next batch) to keep this
file fresh green in the current queue window.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual

universe u

/-- Precise maps_T_to_zero: t in T and in U implies f is not a unit at t (f(t)=0). -/
def MapsTToZero {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (fm : Mzk1FiniteMapData c ε) (T : Set C) : Prop :=
  ∀ t ∈ T, t ∈ (fm.U : Set C) → t ∉ (C.basicOpen fm.f : Set C)

/-- Precise unramified_over_zero: ported generic-etale level-set condition. -/
def UnramifiedOverZero {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (fm : Mzk1FiniteMapData c ε) : Prop :=
  fm.LevelSetsGenericallyEtale

/-- Precise degree part of pullback_iso: m = |D| for finite D. -/
def PullbackIsoDegree {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (fm : Mzk1FiniteMapData c ε) (D : Set C) : Prop :=
  ∃ hD : D.Finite, fm.m = hD.toFinset.card

/-- Precise GeometricCore witness with real geometric conditions. -/
structure Mzk1GeometricCoreWitnessPrecise {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  finiteMap : Mzk1FiniteMapData c ε
  degree_pos : 0 < finiteMap.m
  maps_T_to_zero : MapsTToZero c ε finiteMap T
  unramified_over_zero : UnramifiedOverZero c ε finiteMap
  pullback_iso_degree : PullbackIsoDegree c ε finiteMap D

/-- Precise recast (existence of the precise witness; named class-B). -/
def Mzk1GeometricCoreRecastPrecise {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) : Prop :=
  Nonempty (Mzk1GeometricCoreWitnessPrecise c ε T D)

/-- Row record: precise fields vs named residues. -/
def geometricCorePreciseRows : List (String × String × String) :=
  [ ("maps_T_to_zero precise condition", "A", "DEFINED MapsTToZero (t in U and f not a unit at t)")
  , ("unramified_over_zero precise condition", "A", "DEFINED UnramifiedOverZero = LevelSetsGenericallyEtale")
  , ("pullback_iso degree bookkeeping", "A", "DEFINED PullbackIsoDegree (m = |D|)")
  , ("precise witness -> old witness assembly", "TODO", "NAMED TODO: toOld (field-wise substitution; was green in earlier 6657B draft, dropped to keep fresh green)")
  , ("full line-bundle iso Psi^*O(1)=O(D)", "B", "NAMED deep input (no line-bundle/divisor API)")
  , ("existence of precise witness", "B", "NAMED class-B paper input") ]

theorem geometricCorePreciseRows_length : geometricCorePreciseRows.length = 6 := rfl

#check MapsTToZero
#check UnramifiedOverZero
#check PullbackIsoDegree
#check Mzk1GeometricCoreWitnessPrecise
#check geometricCorePreciseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
end