import tmp.sheaf.xif.paper.Mzk1GeomCoreRRProvedActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: flt_core RR (Mzk1GeomCoreRRProvedActual: zero_divisor_exists_proved, EXIT0 210173 SIZE 15877) + root-neutral bridge interface (Mzk1GeomCoreBridgeInterfaceActual: ZeroDivisorDatum/FibreBridgeAbstract) -> flt_core-side adapter: supply ZeroDivisorDatum from RR; no flt_test/flt_th import (root conflict avoided).

# Mzk1GeomCoreRRBridgeActual — flt_core-side adapter of the root-neutral bridge

Supplies the function-field half of the scheme<->function-field bridge: the RR-proved
zero divisor (zero_divisor_exists_proved) packaged as `ZeroDivisorDatum`, plus a
`FibreBridgeAbstract` builder once the scheme side provides the two named maps
(sectionMap : Gamma(C,U) ->+* F and placePoint : P -> C).  This file imports ONLY the
flt_core root; the flt_test-side adapter is Mzk1GeomCoreBridgeLegacyActual.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRBridgeActual

open KaehlerDifferential
open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual

universe u

section FromRR

variable {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
  [DecidableEq (RatFunc K)] [Field F] [Algebra K F]
  [HasCanonicalDivisor (K := K) (F := F)]
  [∀ w : Place K F, w.DCoordGenerates]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
  [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue] [Nontrivial Ω[F⁄K]]
  [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
  [∀ u : Place K (RatFunc K), u.FiniteResidue]
  [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F]
  [Algebra.IsSeparable (RatFunc K) F]
  [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
  [FiniteDimensional (RatFunc K) F] [HasSeparableResidue K F]

/-- **RR => zero-divisor datum (function-field half of the bridge).**  From the
flt_core-root Riemann-Roch (PROVED) and T finite with |T| >= 2g+1, the root-neutral
`ZeroDivisorDatum` exists.  (Nonempty form: the datum contains data, so it cannot be
eliminated from a Prop existential into Type; the choice version follows below.) -/
theorem zeroDivisorDatum_nonempty_of_RR (T : Finset (Place K F))
    (hcard : 2 * genus K F + 1 ≤ T.card) :
    Nonempty (ZeroDivisorDatum (Place K F) F (fun p f => p.ord f)) := by
  obtain ⟨g, hg0, hzero, hno⟩ := zero_divisor_exists_proved (K := K) (F := F) T hcard
  exact ⟨
    { T := T
      g := g
      g_ne_zero := hg0
      zero_simple := hno
      no_other_zero := by
        intro p hp
        have hnot : ¬ 0 < p.ord g := fun hpos => hp ((hzero p).mp hpos)
        omega }⟩

/-- Choice version of the RR => zero-divisor datum adapter. -/
noncomputable def zeroDivisorDatum_of_RR (T : Finset (Place K F))
    (hcard : 2 * genus K F + 1 ≤ T.card) :
    ZeroDivisorDatum (Place K F) F (fun p f => p.ord f) :=
  Classical.choice (zeroDivisorDatum_nonempty_of_RR (K := K) (F := F) T hcard)

/-- **Bridge builder (flt_core side).**  Once the scheme side supplies the two named
maps (sectionMap, placePoint) and the compatibility hypotheses, they assemble into the
root-neutral `FibreBridgeAbstract`.  This is the exact shape of the missing connection. -/
def bridge_of_maps {X : Type u} {A : Type u} [CommRing A] {F' : Type u} [Field F']
    {U : Set X} {f : A} {basicOpen : Set X}
    (placePoint : Place K F → X) (sectionMap : A →+* F')
    (ord : Place K F → F' → ℤ) (Tplaces : Finset (Place K F))
    (section_ord : ∀ p : Place K F, placePoint p ∈ U →
      (placePoint p ∉ basicOpen ↔ 0 < ord p (sectionMap f)))
    (Tplaces_eq : ∀ p : Place K F, p ∈ Tplaces ↔ 0 < ord p (sectionMap f))
    (surjective : ∀ t : X, t ∈ U → t ∉ basicOpen → ∃ p : Place K F, placePoint p = t)
    (placePoint_mem_U : ∀ p ∈ Tplaces, placePoint p ∈ U) :
    FibreBridgeAbstract X A F' U f basicOpen (Place K F) ord :=
  { placePoint := placePoint
    sectionMap := sectionMap
    Tplaces := Tplaces
    section_ord := section_ord
    Tplaces_eq := Tplaces_eq
    surjective := surjective
    placePoint_mem_U := placePoint_mem_U }

end FromRR

/-- Rows: flt_core-side adapter status + remaining named layers. -/
def rrBridgeRows : List (String × String × String) :=
  [ ("RR => ZeroDivisorDatum", "PROVED", "zeroDivisorDatum_nonempty_of_RR / zeroDivisorDatum_of_RR (zero_divisor_exists_proved; no named input)")
  , ("FibreBridgeAbstract builder", "DEFINED", "bridge_of_maps: assembles the interface from the two named maps + compatibility")
  , ("sectionMap : Gamma(C,U) ->+* F", "NAMED API GAP", "scheme section ring -> function field map does not exist in Mathlib/ported trees")
  , ("placePoint : P -> C", "NAMED API GAP", "function-field place -> scheme point map does not exist")
  , ("finite-map construction fm : Mzk1FiniteMapData", "NAMED INPUT (flt_test root)", "the scheme-side datum is still constructed/assumed in the legacy root; no constructor from a function field")
  , ("root compatibility", "RESOLVED BY LAYERING", "flt_core adapter (this file) and flt_test adapter (Mzk1GeomCoreBridgeLegacyActual) meet only in the root-neutral interface") ]

theorem rrBridgeRows_length : rrBridgeRows.length = 6 := rfl

#check zeroDivisorDatum_nonempty_of_RR
#check zeroDivisorDatum_of_RR
#check bridge_of_maps
#check rrBridgeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRBridgeActual
end