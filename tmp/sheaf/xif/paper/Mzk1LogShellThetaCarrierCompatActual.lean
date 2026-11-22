import tmp.sheaf.xif.paper.Mzk1P58iiCMLFActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1LogShellThetaCarrierCompatActual — model-level log-shell/theta carrier compatibility
(replacement route for the failed P58iiCMLFImage dependency)

STEP 0 prior-art (reused, no new mathematics):
* Mzk1P58iiCMLFActual (CMLFHom concrete model morphisms: mapK/mapUnits/log_comm/p_eq);
* SourceLogShellCarrier (preLogShell/unitLayer/logShell/pStar).

WHAT THIS FILE DOES:
* defines an invariant-preserving CMLF morphism and its identity/composition;
* proves that the unit layer image, pre-log-shell image and log-shell image (the last under
  p*-compatibility) are preserved — the model-level content of the theta-carrier / log-shell
  compatibility;
* records rows; the paper CMLF/Gamma^x_non compatibility stays NAMED.
This file is self-contained w.r.t. the earlier CMLFImage attempt (route superseded because of
an import-order/compile instability; same mathematical content, fresh file).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellThetaCarrierCompatActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual

universe u

/-- A CMLF morphism that preserves the invariant submonoid of units. -/
structure CMLFCarrierHom (D E : SourceLogShellDatum.{u}) extends CMLFHom D E where
  /-- invariant submonoid is preserved. -/
  invariants_map : ∀ u : D.Units, u ∈ D.invariants → toCMLFHom.mapUnits u ∈ E.invariants

/-- Identity invariant-preserving CMLF morphism. -/
def CMLFCarrierHom.id (D : SourceLogShellDatum.{u}) : CMLFCarrierHom D D where
  toCMLFHom := CMLFHom.id D
  invariants_map := fun _ hu => hu

/-- Composition of invariant-preserving CMLF morphisms. -/
def CMLFCarrierHom.comp {D E F : SourceLogShellDatum.{u}}
    (f : CMLFCarrierHom D E) (g : CMLFCarrierHom E F) : CMLFCarrierHom D F where
  toCMLFHom := f.toCMLFHom.comp g.toCMLFHom
  invariants_map := fun u hu => g.invariants_map _ (f.invariants_map u hu)

/-- The unit layer is preserved (model level). -/
theorem CMLFCarrierHom.image_unitLayer {D E : SourceLogShellDatum.{u}}
    (f : CMLFCarrierHom D E) :
    f.toCMLFHom.mapK '' D.unitLayer ⊆ E.unitLayer := by
  rintro _ ⟨a, ⟨u, rfl⟩, rfl⟩
  exact ⟨f.toCMLFHom.mapUnits u, (f.toCMLFHom.log_comm u).symm⟩

/-- The pre-log-shell (invariant image) is preserved. -/
theorem CMLFCarrierHom.image_preLogShell {D E : SourceLogShellDatum.{u}}
    (f : CMLFCarrierHom D E) :
    f.toCMLFHom.mapK '' D.preLogShell ⊆ E.preLogShell := by
  rintro _ ⟨a, ⟨u, hu, rfl⟩, rfl⟩
  exact ⟨f.toCMLFHom.mapUnits u, f.invariants_map u hu, (f.toCMLFHom.log_comm u).symm⟩

/-- The log-shell is preserved under p*-compatibility (model level). -/
theorem CMLFCarrierHom.image_logShell {D E : SourceLogShellDatum.{u}}
    (f : CMLFCarrierHom D E) (hstar : D.pStar = E.pStar) :
    f.toCMLFHom.mapK '' D.logShell ⊆ E.logShell := by
  rintro _ ⟨a, ha, rfl⟩
  have hmem : f.toCMLFHom.mapK ((D.pStar : D.K) * a) ∈ E.preLogShell := by
    exact image_preLogShell f ⟨(D.pStar : D.K) * a, ha, rfl⟩
  have hcast : f.toCMLFHom.mapK ((D.pStar : D.K) * a) =
      (D.pStar : E.K) * f.toCMLFHom.mapK a := by
    rw [map_mul, map_natCast]
  rw [hcast, hstar] at hmem
  exact hmem

/-- Compatibility rows: (vertex/statement, proof, status). -/
def logShellThetaCarrierRows : List (String × String × String) :=
  [ ("unit layer preserved by CMLF carrier homs", "CMLFCarrierHom.image_unitLayer", "PROVED (model level)"),
    ("pre-log-shell preserved", "CMLFCarrierHom.image_preLogShell", "PROVED (model level)"),
    ("log-shell preserved (p* compatibility)", "CMLFCarrierHom.image_logShell (hstar)", "PROVED (model level)"),
    ("invariant-preserving id/comp", "CMLFCarrierHom.id / CMLFCarrierHom.comp", "CONSTRUCTED"),
    ("paper CMLF/Gamma^x_non compatibility", "not asserted: needs paper CMLF_TS categories", "NAMED") ]

/-- The compatibility row record has five rows. -/
theorem logShellThetaCarrierRows_length : logShellThetaCarrierRows.length = 5 := rfl

#check CMLFCarrierHom
#check CMLFCarrierHom.image_unitLayer
#check CMLFCarrierHom.image_preLogShell
#check CMLFCarrierHom.image_logShell
#check logShellThetaCarrierRows_length

end LeanFormal.IUT.XiFPaper.Mzk1LogShellThetaCarrierCompatActual
end
