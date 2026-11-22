import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1P58iiCMLFActual — a concrete model category of CMLF log-coordinate data

STEP 0 prior-art: SourceLogShellCarrier (SourceLogShellDatum: p, K, Units, logMap, invariants)
-> REUSE; this file builds the concrete MODEL of the CMLF_TF^+ objects/morphisms used by
Prop 5.8(ii)'s Gamma^x_non diagram: objects are source log-shell data, morphisms preserve the
log-coordinate map and the units; identities and composition are constructed.

The paper's CMLF_TS^+ categories and the full Gamma^x_non diagram remain NAMED (they require
the topological/field-theoretic structure of CMLF not present in this model).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

universe u

/-- A morphism of the concrete CMLF log-coordinate model: a map of log-coordinate fields and
a map of unit groups compatible with both log maps. -/
structure CMLFHom (D E : SourceLogShellDatum.{u}) where
  /-- the map of log-coordinate fields. -/
  mapK : D.K →+* E.K
  /-- the map of unit groups. -/
  mapUnits : D.Units →* E.Units
  /-- compatibility with the p-adic logarithms. -/
  log_comm : ∀ u : D.Units,
    mapK (D.logMap u).toAdd = (E.logMap (mapUnits u)).toAdd
  /-- the residue characteristic is preserved. -/
  p_eq : D.p = E.p

/-- The identity CMLF morphism. -/
def CMLFHom.id (D : SourceLogShellDatum.{u}) : CMLFHom D D where
  mapK := RingHom.id D.K
  mapUnits := MonoidHom.id D.Units
  log_comm := fun _ => rfl
  p_eq := rfl

/-- Composition of CMLF morphisms. -/
def CMLFHom.comp {D E F : SourceLogShellDatum.{u}} (f : CMLFHom D E) (g : CMLFHom E F) :
    CMLFHom D F where
  mapK := g.mapK.comp f.mapK
  mapUnits := g.mapUnits.comp f.mapUnits
  log_comm := by
    intro u
    rw [RingHom.comp_apply, MonoidHom.comp_apply, f.log_comm, g.log_comm]
  p_eq := f.p_eq.trans g.p_eq

/-- Component computation: composition acts on the field map by composition. -/
@[simp] theorem CMLFHom.comp_mapK {D E F : SourceLogShellDatum.{u}} (f : CMLFHom D E)
    (g : CMLFHom E F) : (f.comp g).mapK = g.mapK.comp f.mapK := rfl

/-- Component computation: composition acts on the unit map by composition. -/
@[simp] theorem CMLFHom.comp_mapUnits {D E F : SourceLogShellDatum.{u}} (f : CMLFHom D E)
    (g : CMLFHom E F) : (f.comp g).mapUnits = g.mapUnits.comp f.mapUnits := rfl

/-- Object carrier of the concrete CMLF model (the source log-shell data). -/
abbrev CMLFObject : Type (u + 1) := SourceLogShellDatum.{u}

/-- The concrete CMLF model rows: (item, concrete content, status). -/
def cmlfModelRows : List (String × String × String) :=
  [ ("CMLF_TF^+ objects (concrete model)", "SourceLogShellDatum (p, K, Units, invariants, logMap)", "CONCRETE MODEL (reused)"),
    ("CMLF morphisms (concrete model)", "CMLFHom: mapK + mapUnits + log compatibility + p preservation", "CONSTRUCTED"),
    ("identity morphism", "CMLFHom.id", "CONSTRUCTED"),
    ("composition", "CMLFHom.comp with component laws", "CONSTRUCTED"),
    ("paper CMLF_TS^+ categories", "not constructed (needs the topological/field structure of CMLF_TF/T in [AbsTopIII])", "NAMED"),
    ("Gamma^x_non diagram in CMLF", "not constructed (named N1 of Prop 5.8(ii))", "NAMED") ]

/-- The CMLF model row record has six rows. -/
theorem cmlfModelRows_length : cmlfModelRows.length = 6 := rfl

#check CMLFHom
#check CMLFHom.id
#check CMLFHom.comp
#check CMLFHom.comp_mapK
#check CMLFHom.comp_mapUnits
#check CMLFObject
#check cmlfModelRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual
end
