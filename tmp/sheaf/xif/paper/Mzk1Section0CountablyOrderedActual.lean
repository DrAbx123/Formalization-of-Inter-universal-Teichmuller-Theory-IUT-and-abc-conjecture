import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
# Mzk1Section0CountablyOrderedActual — order-isomorphism invariance of orderwise
connectedness / countably ordered sets (corpus Section 0, l.1277-1292)

STEP 0 prior-art: AbsTopIII05Section0ObjectsActual (OrderwiseConnected, CountablyOrdered,
countablyOrdered_int/_Icc) -> REUSE; this file proves that order isomorphisms transport
orderwise connected subsets and countably-ordered structures.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u v

/-- Orderwise connectedness is preserved by order isomorphisms (corpus l.1277-1280). -/
theorem orderwiseConnected_image {E : Type u} {F : Type v} [Preorder E] [Preorder F]
    (e : E ≃o F) {E' : Set E} (h : OrderwiseConnected E') :
    OrderwiseConnected (e '' E') := by
  rintro c ⟨a, ⟨a0, ha0, rfl⟩, hac⟩ ⟨b, ⟨b0, hb0, rfl⟩, hcb⟩
  have hac' : a0 < e.symm c := by
    simpa using e.symm.lt_iff_lt.mpr hac
  have hcb' : e.symm c < b0 := by
    simpa using e.symm.lt_iff_lt.mpr hcb
  exact ⟨e.symm c, h ⟨a0, ha0, hac'⟩ ⟨b0, hb0, hcb'⟩, by simp⟩

/-- Countably ordered sets are invariant under order isomorphisms. -/
theorem countablyOrdered_of_orderIso {E : Type u} {F : Type v} [Preorder E] [Preorder F]
    (e : E ≃o F) (hE : CountablyOrdered E) : CountablyOrdered F := by
  obtain ⟨E', hconn, ⟨iso⟩⟩ := hE
  exact ⟨E', hconn, ⟨e.symm.trans iso⟩⟩

/-- Countably ordered set structure is an order-isomorphism invariant (both directions). -/
theorem countablyOrdered_iff_of_orderIso {E : Type u} {F : Type v} [Preorder E] [Preorder F]
    (e : E ≃o F) : CountablyOrdered E ↔ CountablyOrdered F :=
  ⟨countablyOrdered_of_orderIso e, countablyOrdered_of_orderIso e.symm⟩

/-- The countably ordered structure transports to any order-isomorphic type. -/
theorem countablyOrdered_of_iso_int {E : Type u} [Preorder E] (e : E ≃o ℤ) :
    CountablyOrdered E :=
  countablyOrdered_of_orderIso e.symm countablyOrdered_int

/-- Invariance rows: (item, statement, status). -/
def countablyOrderedRows : List (String × String × String) :=
  [ ("orderwise connectedness preserved by order isomorphisms", "orderwiseConnected_image", "PROVED"),
    ("countably ordered sets invariant under order isomorphisms", "countablyOrdered_of_orderIso", "PROVED"),
    ("countably ordered <=> under an order isomorphism", "countablyOrdered_iff_of_orderIso", "PROVED"),
    ("any type order-isomorphic to Z is countably ordered", "countablyOrdered_of_iso_int", "PROVED"),
    ("subtypes of Z that are orderwise connected", "countablyOrdered_Icc (Section0Objects) + invariance", "PROVED (partial)") ]

/-- The invariance row record has five rows. -/
theorem countablyOrderedRows_length : countablyOrderedRows.length = 5 := rfl

#check orderwiseConnected_image
#check countablyOrdered_of_orderIso
#check countablyOrdered_iff_of_orderIso
#check countablyOrdered_of_iso_int
#check countablyOrderedRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedActual
end
