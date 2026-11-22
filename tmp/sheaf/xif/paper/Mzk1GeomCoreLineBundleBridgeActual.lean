import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: uniformizer/order compatibility of psi^*O(1)=O(D) (Lead A445) -> root-neutral line-bundle interface (Mzk1GeomCoreLineBundleInterfaceActual: LineBundlePullbackInterface + degree transfer) + root-neutral bridge interface (Mzk1GeomCoreBridgeInterfaceActual: FibreBridgeAbstract section_ord/Tplaces_eq) -> typed compatibility structure + PROVED order-transfer theorems; actual sheaf/pullback remain named.

# Mzk1GeomCoreLineBundleBridgeActual — order/zero-locus compatibility of the line-bundle interface

CLOSES (typed, conditional on explicit compatibility data) the previously-named item
'iso compatibility with uniformizer/order data':
* LineBundleOrderCompatibility: same distinguished section (L.f = f) and the linear
  equivalence agrees with the bridge sectionMap on scheme-side sections;
* order_pos_iff: on U, `placePoint p notin basicOpen <-> 0 < ord p (iso image of f)`;
* Tplaces_order_pos: places over T get positive order of the section image.
STILL NAMED (text only): actual sheaf O(D) and actual pullback psi^* on line bundles.
Root-neutral (imports only the two Mathlib-only interfaces).  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual

universe u v w q

open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual

/-- Typed compatibility between the line-bundle interface and the bridge: the same
section and agreement of the linear equivalence with the bridge section map on
scheme-side sections. -/
structure LineBundleOrderCompatibility {R : Type u} [CommRing R]
    {X : Type v} {A : Type w} [CommRing A] [Algebra R A]
    {F : Type q} [Field F] [Algebra R F]
    {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}
    (B : FibreBridgeAbstract X A F U f basicOpen P ord)
    (L : LineBundlePullbackInterface R A F) where
  /-- the distinguished section is the bridge section -/
  section_eq : L.f = f
  /-- the module-level iso agrees with the bridge section map on scheme-side sections -/
  iso_sectionMap : ∀ (s : A) (hs : s ∈ L.schemeSections),
    (L.iso ⟨s, hs⟩ : F) = B.sectionMap s

section Transfer

variable {R : Type u} [CommRing R] {X : Type v} {A : Type w} [CommRing A] [Algebra R A]
  {F : Type q} [Field F] [Algebra R F]
  {U : Set X} {f : A} {basicOpen : Set X} {P : Type*} {ord : P → F → ℤ}
  {B : FibreBridgeAbstract X A F U f basicOpen P ord}
  {L : LineBundlePullbackInterface R A F}

/-- The iso image of the distinguished section equals the bridge's function-field
section (PROVED). -/
theorem iso_image_f_eq_sectionMap (K : LineBundleOrderCompatibility B L) :
    (L.iso ⟨L.f, L.f_mem⟩ : F) = B.sectionMap f := by
  rw [K.iso_sectionMap L.f L.f_mem, K.section_eq]

/-- **Order transfer (PROVED):** on U, the zero-locus condition for the scheme section
is equivalent to positivity of the order of the iso image of the line-bundle section. -/
theorem order_pos_iff (K : LineBundleOrderCompatibility B L) (p : P)
    (hU : B.placePoint p ∈ U) :
    B.placePoint p ∉ basicOpen ↔
      0 < ord p (L.iso ⟨L.f, L.f_mem⟩ : F) := by
  rw [B.section_ord p hU, iso_image_f_eq_sectionMap K]

/-- **Places over T have positive order (PROVED).** -/
theorem Tplaces_order_pos (K : LineBundleOrderCompatibility B L) (p : P)
    (hp : p ∈ B.Tplaces) : 0 < ord p (L.iso ⟨L.f, L.f_mem⟩ : F) := by
  have hpos : 0 < ord p (B.sectionMap f) := (B.Tplaces_eq p).mp hp
  simpa [iso_image_f_eq_sectionMap K] using hpos

end Transfer

/-- Row record: proved compatibility vs remaining named layers. -/
def lineBundleBridgeRows : List (String × String × String) :=
  [ ("typed line-bundle<->bridge compatibility", "DEFINED", "LineBundleOrderCompatibility (section_eq + iso_sectionMap)")
  , ("iso image of f = bridge section map f", "PROVED", "iso_image_f_eq_sectionMap")
  , ("uniformizer/order compatibility on U", "PROVED (conditional)", "order_pos_iff: placePoint p notin basicOpen <-> 0 < ord p (iso image of f)")
  , ("places over T positive order", "PROVED", "Tplaces_order_pos")
  , ("actual sheaf O(D) on the scheme", "NAMED GAP", "no Cartier-divisor/line-bundle API")
  , ("actual pullback psi^* on line bundles", "NAMED GAP", "no projective-scheme morphism/line-bundle pullback API") ]

theorem lineBundleBridgeRows_length : lineBundleBridgeRows.length = 6 := rfl

#check LineBundleOrderCompatibility
#check iso_image_f_eq_sectionMap
#check order_pos_iff
#check Tplaces_order_pos
#check lineBundleBridgeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleBridgeActual
end