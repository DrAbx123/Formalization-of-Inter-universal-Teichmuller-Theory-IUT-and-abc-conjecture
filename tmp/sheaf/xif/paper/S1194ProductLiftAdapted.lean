import tmp.sheaf.xif.paper.S1184NonReflKummerActual
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitUnitsActionSupply

/-! # S1194: product lift of the non-refl Kummer isomorphism -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1194ProductLiftAdapted

open LeanFormal.IUT
open LeanFormal.IUT.TimesMuKummer

universe u v uv

variable {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- Open image of an open subgroup under a continuous open homomorphism. -/
def _root_.OpenSubgroup.mapOfOpenMap (K : OpenSubgroup G) (f : G →* H)
    (hf : Continuous f) (hopen : IsOpenMap f) : OpenSubgroup H where
  toSubgroup := (K : Subgroup G).map f
  isOpen' := by
    change IsOpen (f '' (K : Set G))
    exact hopen _ K.isOpen

/-- Fixed subgroup of a precomposed action equals the fixed subgroup of the
image open subgroup. -/
theorem fixedSubgroup_comp_eq_map
    {U : Type v} [CommGroup U]
    (rho : H →* MulAut U) (f : G →* H) (K : OpenSubgroup G)
    (hf : Continuous f) (hopen : IsOpenMap f) :
    TimesMuKummer.fixedSubgroup (rho.comp f) K =
      TimesMuKummer.fixedSubgroup rho (K.mapOfOpenMap f hf hopen) := by
  ext u
  constructor
  · intro hu
    rintro h
    rcases h.2 with ⟨g, hg, hfg⟩
    rw [← hfg]
    exact hu ⟨g, hg, rfl⟩
  · intro hu g
    exact hu ⟨f g.1, ⟨g.1, g.2, rfl⟩⟩

end LeanFormal.IUT.XiFPaper.S1194ProductLiftAdapted

end
