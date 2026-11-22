import tmp.sheaf.xif.paper.Mzk1P58iiCMLFActual

/-!
# Mzk1CMLFCategoryLawActual — category laws for the concrete CMLF model (CMLF_TS/TF model
component). New theorems: composition associativity and identity laws on both components.
No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CMLFCategoryLawActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual

universe u

/-- Derived category law: associativity on the field-map component. -/
theorem CMLFHom.comp_assoc_mapK {D E F G : SourceLogShellDatum.{u}}
    (f : CMLFHom D E) (g : CMLFHom E F) (h : CMLFHom F G) :
    ((f.comp g).comp h).mapK = (f.comp (g.comp h)).mapK := by
  rw [CMLFHom.comp_mapK, CMLFHom.comp_mapK, CMLFHom.comp_mapK, CMLFHom.comp_mapK,
    RingHom.comp_assoc]

/-- Derived category law: associativity on the unit-map component. -/
theorem CMLFHom.comp_assoc_mapUnits {D E F G : SourceLogShellDatum.{u}}
    (f : CMLFHom D E) (g : CMLFHom E F) (h : CMLFHom F G) :
    ((f.comp g).comp h).mapUnits = (f.comp (g.comp h)).mapUnits := by
  rw [CMLFHom.comp_mapUnits, CMLFHom.comp_mapUnits, CMLFHom.comp_mapUnits,
    CMLFHom.comp_mapUnits, MonoidHom.comp_assoc]

/-- Derived category law: left identity on the field-map component. -/
theorem CMLFHom.id_comp_mapK {D E : SourceLogShellDatum.{u}} (f : CMLFHom D E) :
    ((CMLFHom.id D).comp f).mapK = f.mapK := by
  rw [CMLFHom.comp_mapK]
  simp [CMLFHom.id]

/-- Derived category law: left identity on the unit-map component. -/
theorem CMLFHom.id_comp_mapUnits {D E : SourceLogShellDatum.{u}} (f : CMLFHom D E) :
    ((CMLFHom.id D).comp f).mapUnits = f.mapUnits := by
  rw [CMLFHom.comp_mapUnits]
  simp [CMLFHom.id]

/-- Derived category law: right identity on the field-map component. -/
theorem CMLFHom.comp_id_mapK {D E : SourceLogShellDatum.{u}} (f : CMLFHom D E) :
    (f.comp (CMLFHom.id E)).mapK = f.mapK := by
  rw [CMLFHom.comp_mapK]
  simp [CMLFHom.id]

/-- Derived category law: right identity on the unit-map component. -/
theorem CMLFHom.comp_id_mapUnits {D E : SourceLogShellDatum.{u}} (f : CMLFHom D E) :
    (f.comp (CMLFHom.id E)).mapUnits = f.mapUnits := by
  rw [CMLFHom.comp_mapUnits]
  simp [CMLFHom.id]

#check CMLFHom.comp_assoc_mapK
#check CMLFHom.comp_assoc_mapUnits
#check CMLFHom.id_comp_mapK
#check CMLFHom.id_comp_mapUnits
#check CMLFHom.comp_id_mapK
#check CMLFHom.comp_id_mapUnits

end LeanFormal.IUT.XiFPaper.Mzk1CMLFCategoryLawActual
end
