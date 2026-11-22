import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1Prop58iImagesActual — concrete image descriptions for Prop 5.8(i)/(ii) invariants

STEP 0 prior-art: SourceLogShellCarrier (SourceLogShellDatum, preLogShell/unitLayer/logShell
definitions), Mzk1Prop58iConcreteActual (concrete invariants, p* formula) -> REUSE; this file
adds the exact SET-EQUALITY descriptions of the unit/invariant/log-shell images that the
paper's Prop 5.8 refers to (normally these are definitional, and here they are proved by rfl),
plus the p*-scaling description of the log-shell.

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iImagesActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

universe u

/-- The invariant image (pre-log-shell) is exactly the log-image of the invariant submonoid
(corpus Prop 5.8(i)/(ii), l.8059-8100). -/
theorem preLogShell_eq_image_invariants (D : SourceLogShellDatum.{u}) :
    D.preLogShell = (fun u : D.Units => (D.logMap u).toAdd) '' (D.invariants : Set D.Units) := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

/-- The unit image (unit layer) is exactly the log-image of all units. -/
theorem unitLayer_eq_image_units (D : SourceLogShellDatum.{u}) :
    D.unitLayer = (fun u : D.Units => (D.logMap u).toAdd) '' (Set.univ : Set D.Units) := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Set.mem_univ u, rfl⟩
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩

/-- The log-shell is exactly the p*-inverse-scaled pre-log-shell
(corpus Prop 5.8(i)/(ii), IUTchIII Def 1.1(i)). -/
theorem logShell_eq_pStar_invScaled_preLogShell (D : SourceLogShellDatum.{u}) :
    D.logShell = {a : D.K | (D.pStar : D.K) * a ∈ D.preLogShell} := by
  ext a
  constructor
  · intro ha
    exact ha
  · intro ha
    exact ha

/-- The invariant submonoid image lies in the unit image (trivial inclusion of the model). -/
theorem preLogShell_subset_unitLayer (D : SourceLogShellDatum.{u}) :
    D.preLogShell ⊆ D.unitLayer := by
  intro a ha
  rcases ha with ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

/-- Image-description rows: (item, exact description, status). -/
def prop58iImageRows : List (String × String × String) :=
  [ ("invariant image (pre-log-shell)", "preLogShell = logMap '' invariants", "PROVED (set equality)"),
    ("unit image (unit layer)", "unitLayer = logMap '' univ(Units)", "PROVED (set equality)"),
    ("log-shell", "logShell = {a | p* · a ∈ preLogShell}", "PROVED (set equality)"),
    ("inclusion of invariant image into unit image", "preLogShell ⊆ unitLayer", "PROVED"),
    ("p* formula", "sourceLogShellStar p = if p = 2 then p^2 else p (prime p)", "PROVED (P58I)") ]

/-- The image-description row record has five rows. -/
theorem prop58iImageRows_length : prop58iImageRows.length = 5 := rfl

#check preLogShell_eq_image_invariants
#check unitLayer_eq_image_units
#check logShell_eq_pStar_invScaled_preLogShell
#check preLogShell_subset_unitLayer
#check prop58iImageRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iImagesActual
end
