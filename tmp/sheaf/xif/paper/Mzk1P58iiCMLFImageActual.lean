import tmp.sheaf.xif.paper.Mzk1P58iiCMLFActual

/-!
# Mzk1P58iiCMLFImageActual — image functoriality of the CMLF model morphisms

STEP 0 prior-art: Mzk1P58iiCMLFActual (CMLFHom concrete model morphisms with log
compatibility and p-preservation), SourceLogShellCarrier (preLogShell/unitLayer/logShell)
-> REUSE; this file proves the image-preservation statements of the Gamma^x_non diagram
vertices under invariant-preserving CMLF morphisms (model level).

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFImageActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual

universe u

/-- A CMLF morphism that preserves the invariant submonoid (needed for pre-log-shell and
log-shell image functoriality). -/
structure CMLFInvariantHom (D E : SourceLogShellDatum.{u}) extends CMLFHom D E where
  invariants_map : ∀ u : D.Units, u ∈ D.invariants → toCMLFHom.mapUnits u ∈ E.invariants

/-- The identity CMLF morphism preserves invariants. -/
def CMLFInvariantHom.id (D : SourceLogShellDatum.{u}) : CMLFInvariantHom D D where
  toCMLFHom := CMLFHom.id D
  invariants_map := fun _ hu => hu

/-- Composition of invariant-preserving CMLF morphisms. -/
def CMLFInvariantHom.comp {D E F : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) (g : CMLFInvariantHom E F) : CMLFInvariantHom D F where
  toCMLFHom := f.toCMLFHom.comp g.toCMLFHom
  invariants_map := by
    intro u hu
    exact g.invariants_map _ (f.invariants_map u hu)

/-- The unit layer is preserved by every CMLF morphism (model level). -/
theorem CMLFInvariantHom.image_unitLayer {D E : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) :
    f.toCMLFHom.mapK '' D.unitLayer ⊆ E.unitLayer := by
  rintro _ ⟨a, ⟨u, rfl⟩, rfl⟩
  exact ⟨f.toCMLFHom.mapUnits u, (f.toCMLFHom.log_comm u).symm⟩

/-- The pre-log-shell (invariant image) is preserved by invariant-preserving CMLF
morphisms. -/
theorem CMLFInvariantHom.image_preLogShell {D E : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) :
    f.toCMLFHom.mapK '' D.preLogShell ⊆ E.preLogShell := by
  rintro _ ⟨a, ⟨u, hu, rfl⟩, rfl⟩
  exact ⟨f.toCMLFHom.mapUnits u, f.invariants_map u hu, (f.toCMLFHom.log_comm u).symm⟩

/-- The log-shell is preserved by invariant-preserving CMLF morphisms (using p-preservation
and the model definition logShell = p*^{-1} preLogShell). -/
theorem CMLFInvariantHom.image_logShell {D E : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) (hstar : D.pStar = E.pStar) :
    f.toCMLFHom.mapK '' D.logShell ⊆ E.logShell := by
  rintro _ ⟨a, ha, rfl⟩
  -- ha : (D.pStar : D.K) * a ∈ D.preLogShell
  have hmem : f.toCMLFHom.mapK ((D.pStar : D.K) * a) ∈ E.preLogShell := by
    exact image_preLogShell f ⟨(D.pStar : D.K) * a, ha, rfl⟩
  have hcast : f.toCMLFHom.mapK ((D.pStar : D.K) * a) =
      (D.pStar : E.K) * f.toCMLFHom.mapK a := by
    rw [map_mul, map_natCast]
  rw [hcast, hstar] at hmem
  exact hmem

/-- Model functoriality rows: (vertex/statement, proof, status). -/
def cmlfImageRows : List (String × String × String) :=
  [ ("unit layer preserved", "CMLFInvariantHom.image_unitLayer", "PROVED (model level)"),
    ("pre-log-shell preserved by invariant-preserving morphisms", "CMLFInvariantHom.image_preLogShell", "PROVED (model level)"),
    ("log-shell preserved (under p* compatibility)", "CMLFInvariantHom.image_logShell (hstar)", "PROVED (model level)"),
    ("invariant-preserving id/comp", "CMLFInvariantHom.id / CMLFInvariantHom.comp", "CONSTRUCTED"),
    ("Gamma^x_non diagram functoriality in CMLF", "not claimed (needs paper CMLF_TS^+ categories)", "NAMED") ]

/-- The image-functoriality row record has five rows. -/
theorem cmlfImageRows_length : cmlfImageRows.length = 5 := rfl

#check CMLFInvariantHom
#check CMLFInvariantHom.image_unitLayer
#check CMLFInvariantHom.image_preLogShell
#check CMLFInvariantHom.image_logShell
#check cmlfImageRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFImageActual
end
