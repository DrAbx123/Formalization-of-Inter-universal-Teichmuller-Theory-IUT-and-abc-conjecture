/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1S1902BridgeInterfaceActual

/-!
# A631 LANA BRIDGE AUDIT (statement-only; mainline)

**Read-only audit record.  This file does NOT import the external lana repository,
does NOT change any canonical object, and its contents are NOT counted as closing our
two gaps.**

External evidence surveyed (textual references only): `tmp/online/lana-agents__iut/iut-main`.

## What lana proves (no `sorry`/`axiom` in `Iut/`; only a `sorry` in the isolated
`Comparator/Challenge.lean`)

* IUT IV Theorem 1.10 invariants (R4, Steps (ii),(iii)): `TowerArithmetic` and
  `TowerArithmetic.certificate : Theorem110Certificate`
  (`Iut/Concrete/Invariants.lean:287`, `:310`); for the tripod the tower arithmetic is
  proved unconditionally (`Iut/Tripod/Tower.lean:79` with `towerLocalHyp` from
  `Iut/Tripod/TameTwo.lean:241`).
* Theorem 1.10 Steps (iv)-(vii) local estimates: the structure `LocalEstimate`
  (`Iut/Implication/LogVolumeBound.lean:72`) is CONSTRUCTED from local-field theory by
  `TowerArithmetic.localEstimate` (`Iut/Concrete/LocalEstimate.lean:460`).
* Consequence: `LocalEstimate.rhs_le` (`Iut/Implication/LogVolumeBound.lean:210`):
  `rhs = -|log Theta| <= procession-average of (capsuleBound + n*log(sqrt 2 * pi))`;
  here `rhs` is the procession-normalized log-volume of the theta-pilot hull
  (`Iut/Cor312/RightHandSide.lean:107`).
* `ConcreteThetaDataExistence` is proved (`Iut/Tripod/Main.lean:84`).

## What lana does NOT prove; the boundary is the SAME as ours

* `Iut.Corollary312Variant` is a `Prop`-valued DEFINITION
  (`Iut/Cor312/Statement.lean:89-95`), documented as deliberately left without proof
  and without axioms; `Cor312VariantHolds` (`Iut/Concrete/ThetaRegion.lean:375`) is
  likewise unproved.  The main theorem `Iut.classicalABC_of_variant
  (h312 : Cor312VariantHolds) : ClassicalABC` (`Iut/MainTheorem.lean:36`) takes
  Corollary 3.12 as an explicit hypothesis.
* Hence in lana the direction is: **Theorem 1.10 (local estimates + `rhs_le`) is used
  inside the `Cor312VariantHolds => ABC` reduction**; it is NOT a proof of Corollary
  3.12 and NOT a proof of our two comparison inequalities.
* Environment mismatch: lana's toolchain is `leanprover/lean4:v4.32.0` with 22 lake
  deps and `mathlib@81a5d257c8`, while this repository is pinned to
  `mathlib@905b95818e`; the external repository is not in our `lakefile`, so
  **direct `import` is impossible**.  Only textual references are recorded here.

## Correspondence with our two concrete gaps (Prop-level record only)

* our `Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume` (Gap 1:
  IUT IV arithmetic line-bundle height comparison) has **no counterpart** in lana;
* our `Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight` (Gap 2:
  comparison-region log-volume bounded by `(1+eps)*arithmeticWeight + theta-hull bound
  + D`) is **not** lana's `rhs_le`: lana bounds the theta-pilot hull log-volume in its
  own packet/container framework, while our Gap 2 bounds the log-volume of the ABC-point
  comparison region on `S1902Carrier`; they belong to the same paper estimate family
  (IUT IV Theorem 1.10 Step (v) plus the arithmetic dictionary) but are different Lean
  objects, and no Lean transfer exists.

`lanaAuditRows` below records the row-by-row audit; `gaps_of_tripleComparison` records
our two gap Props on the canonical triple-dependent comparison region.  Neither is
evidence of gap closure.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace Mzk1LanaBridgeAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

/-- Our **Gap 1** in Prop form: the height comparison against the region log-volume. -/
def Gap1Prop {X : Type*} (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (W.logVolume (region a b c)).toReal

/-- Our **Gap 2** in Prop form: the region log-volume bound by the arithmetic weight,
  the theta-hull bound, and a per-`ε` constant. -/
def Gap2Prop {X : Type*} (W : LeanFormal.IUT.IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (region a b c)).toReal ≤
      (1 + ε) * arithmeticWeight (abcRationalPoint a c) + (W.logVolume W.hull).toReal + D

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The two gap Props extracted from the canonical triple-dependent comparison data
  (`Mzk1PaperComparisonRegionScalingActual.TripleDependentComparison`). -/
theorem gaps_of_tripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    Gap1Prop (s1902IQHullLogVolumeInterface T)
        (paperComparisonRegion T point) ∧
      Gap2Prop (s1902IQHullLogVolumeInterface T)
        (paperComparisonRegion T point) := 
  ⟨C.height_le_regionVolume, C.regionVolume_le_weight⟩

/-- Row-by-row audit table: object, external reference, status. -/
def lanaAuditRows : List (String × String × String) :=
  [ ("lana Thm1.10 invariants (R4, Steps ii-iii)",
      "Iut/Concrete/Invariants.lean:287,310 (TowerArithmetic, certificate)",
      "GREEN in lana; textual reference only"),
    ("lana Thm1.10 Steps (iv)-(vii) local estimates",
      "Iut/Concrete/LocalEstimate.lean:460 (TowerArithmetic.localEstimate)",
      "GREEN in lana; textual reference only"),
    ("lana theta-hull upper bound",
      "Iut/Implication/LogVolumeBound.lean:210 (LocalEstimate.rhs_le)",
      "GREEN in lana; different objects from our Gap 2"),
    ("lana concrete Theta-data existence",
      "Iut/Tripod/Main.lean:84 (concreteThetaDataExistence')",
      "GREEN in lana; textual reference only"),
    ("lana Corollary 3.12 variant statement",
      "Iut/Cor312/Statement.lean:89-95 (Corollary312Variant)",
      "UNPROVED specification boundary (same as ours)"),
    ("lana Corollary 3.12 hypothesis",
      "Iut/Concrete/ThetaRegion.lean:375 (Cor312VariantHolds)",
      "UNPROVED; explicit hypothesis"),
    ("lana main ABC theorem",
      "Iut/MainTheorem.lean:36 (classicalABC_of_variant)",
      "CONDITIONAL on Cor312VariantHolds"),
    ("our Gap 1", "height_le_normalizedRegionVolume",
      "NAMED; no lana counterpart"),
    ("our Gap 2", "regionVolume_le_normalizedWeight",
      "NAMED; NOT lana rhs_le (different objects)"),
    ("environment", "lana: v4.32.0, mathlib@81a5d257c8; ours: mathlib@905b95818e",
      "direct import IMPOSSIBLE"),
    ("scope", "audit record only; NOT gap closure", "INTEGRITY") ]

theorem lanaAuditRows_length : lanaAuditRows.length = 11 := rfl

/-! ### Axiom gates (local theorems only; lana statements are textual references) -/

#print axioms gaps_of_tripleComparison
#print axioms lanaAuditRows_length

end Mzk1LanaBridgeAuditActual

end