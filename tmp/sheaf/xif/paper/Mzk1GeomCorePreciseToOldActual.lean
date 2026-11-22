/-
# Mzk1GeomCorePreciseToOldActual — precise -> old GeometricCore witness conversion (H6)

STEP 0 prior-art: the conversion was green in an earlier 6657B draft of
`Mzk1GeometricCorePreciseActual.lean` but was removed to keep that file fresh green;
its docstring and `geometricCorePreciseRows` row 4 record it as a NAMED TODO
("precise witness -> old witness assembly: TODO").  This file restores it as a
separate file; no existing file is modified.

Objects (exact sources):
* old witness: `Mzk1GeometricCoreRealStructureActual.lean:53-64`
  (`Mzk1GeometricCoreWitness` with the three *free* `Prop` fields
  `maps_T_to_zero`, `unramified_over_zero`, `pullback_iso` and their proofs)
  and old recast `:67-71` (`Mzk1GeometricCoreRecast := Nonempty witness`);
* precise witness: `Mzk1GeometricCorePreciseActual.lean:53-60`
  (`Mzk1GeometricCoreWitnessPrecise` with the three geometric conditions
  `MapsTToZero`, `UnramifiedOverZero := fm.LevelSetsGenericallyEtale`,
  `PullbackIsoDegree`) and precise recast `:63-66`.

The conversion is a field-wise substitution: each free `Prop` of the old witness is
instantiated with the corresponding precise condition, and its proof field with the
corresponding precise field.  No unproved steps, no extra assumptions, no placeholders.

Consumer link: `GenEll15GeometricCoreStatement`
(`GenEll15GeometricCoreAssemblyActual.lean:48-52`) is
`∀ {R} [CommRing R] {C} (c) (ε) (T D), Mzk1GeometricCoreRecast c ε T D` over the
OLD witness, so the precise existence statement at every datum yields it through
`toOldRecast` (`genEll15GeometricCoreStatement_of_precise` below).  The precise
statement itself is the named class-B input; it is stated, not proved here.
-/

import tmp.sheaf.xif.paper.Mzk1GeometricCorePreciseActual
import tmp.sheaf.xif.paper.GenEll15GeometricCoreAssemblyActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCorePreciseToOldActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.GenEll15GeometricCoreAssemblyActual

universe u

/-- **Precise witness -> old witness (field-wise substitution).**  The old free
`Prop` fields are instantiated with the precise conditions `MapsTToZero`,
`UnramifiedOverZero`, `PullbackIsoDegree` of the precise witness, and the old proof
fields with the precise condition proofs.  The finite map and degree positivity are
carried over unchanged. -/
def toOldWitness {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPrecise c ε T D) :
    Mzk1GeometricCoreWitness c ε T D where
  finiteMap := w.finiteMap
  degree_pos := w.degree_pos
  maps_T_to_zero := MapsTToZero c ε w.finiteMap T
  maps_T_to_zero_proof := w.maps_T_to_zero
  unramified_over_zero := UnramifiedOverZero c ε w.finiteMap
  unramified_over_zero_proof := w.unramified_over_zero
  pullback_iso := PullbackIsoDegree c ε w.finiteMap D
  pullback_iso_proof := w.pullback_iso_degree

/-- The finite map is carried over definitionally. -/
@[simp] theorem toOldWitness_finiteMap {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPrecise c ε T D) :
    (toOldWitness w).finiteMap = w.finiteMap := rfl

/-- The old `pullback_iso` field is exactly the precise degree condition. -/
theorem toOldWitness_pullback_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPrecise c ε T D) :
    (toOldWitness w).pullback_iso = PullbackIsoDegree c ε w.finiteMap D := rfl

/-- The old `maps_T_to_zero` field is exactly the precise condition. -/
theorem toOldWitness_maps_T_to_zero {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPrecise c ε T D) :
    (toOldWitness w).maps_T_to_zero = MapsTToZero c ε w.finiteMap T := rfl

/-- The old `unramified_over_zero` field is exactly the precise condition. -/
theorem toOldWitness_unramified_over_zero {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPrecise c ε T D) :
    (toOldWitness w).unramified_over_zero = UnramifiedOverZero c ε w.finiteMap := rfl

/-- **Precise recast -> old recast** (`Nonempty` of precise witnesses gives
`Nonempty` of old witnesses). -/
theorem toOldRecast {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (h : Mzk1GeometricCoreRecastPrecise c ε T D) :
    Mzk1GeometricCoreRecast c ε T D :=
  h.elim fun w => ⟨toOldWitness w⟩

/-- The precise analogue of the consumer statement: at every curve datum the precise
witness exists.  (Named class-B paper input; not proved here.) -/
def GenEll15GeometricCoreStatementPrecise : Prop :=
  ∀ {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
    Mzk1GeometricCoreRecastPrecise c ε T D

/-- **Consumer link:** the precise existence statement yields
`GenEll15GeometricCoreStatement` (the statement consumed by
`GenEll15GeometricCoreAssemblyActual`), datum by datum through `toOldRecast`. -/
theorem genEll15GeometricCoreStatement_of_precise
    (h : GenEll15GeometricCoreStatementPrecise.{u}) :
    GenEll15GeometricCoreStatement.{u} :=
  fun c ε T D => toOldRecast (h c ε T D)

/-- Row record: what is now proved in this file vs the named class-B residual. -/
def preciseToOldRows : List (String × String × String) :=
  [ ("precise witness -> old witness", "A", "PROVED toOldWitness (field-wise substitution)")
  , ("precise recast -> old recast", "A", "PROVED toOldRecast (Nonempty.elim)")
  , ("precise existence statement -> GenEll15GeometricCoreStatement", "A", "PROVED genEll15GeometricCoreStatement_of_precise")
  , ("existence of the precise witness", "B", "NAMED class-B paper input (GenEll15GeometricCoreStatementPrecise; not proved)") ]

/-- The row record has four rows. -/
theorem preciseToOldRows_length : preciseToOldRows.length = 4 := rfl

#check toOldWitness
#check toOldRecast
#check GenEll15GeometricCoreStatementPrecise
#check genEll15GeometricCoreStatement_of_precise
#check preciseToOldRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCorePreciseToOldActual
end
