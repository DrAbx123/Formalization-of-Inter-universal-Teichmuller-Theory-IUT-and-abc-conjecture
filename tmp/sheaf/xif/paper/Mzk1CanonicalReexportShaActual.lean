import tmp.sheaf.xif.paper.Mzk1S1902BridgeInterfaceActual
import tmp.sheaf.xif.paper.Mzk1S1902IQHullInterfaceActual

/-!
# shehdd A623 canonical re-export (Sha, thin, import fixed)

Read-only re-exports of the canonical S1902 data now that both canonical files are
green: hull's concrete `s1902IQHullInterface` instance and mainline's canonical
bridge `s1902Bridge`/`s1902Bridge_abc` (gate printed below).  Canonical files are
owned by hull/mainline; this file only imports them and adds thin projections.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalReexportShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Read-only re-export: hull's canonical concrete IQ hull interface. -/
noncomputable def reexportHullData : IQHullLogVolumeInterface (S1902Carrier T) :=
  s1902IQHullInterface T

theorem reexportHullData_hull_eq : (reexportHullData T).hull = s1902Hull T :=
  rfl

theorem reexportHullData_imageSet_subset :
    (reexportHullData T).imageSet ⊆ s1902Hull T :=
  (reexportHullData T).imageSet_subset_hull

theorem reexportHullData_hull_logVolume_lt_top :
    (reexportHullData T).logVolume (reexportHullData T).hull < ⊤ :=
  (reexportHullData T).hull_logVolume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1CanonicalReexportShaActual

/-! ### Axiom gate for the canonical mainline bridge (read-only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual.s1902Bridge_abc
