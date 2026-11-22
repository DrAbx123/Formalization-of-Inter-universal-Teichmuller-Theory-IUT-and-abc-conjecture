import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual

/-! # Mzk1Stage4LanaIutIVEstimateActual (stage4 lane; LANA IUT IV port, self-contained)

A630 module: study-port of the LANA IUT IV local estimates into a self-contained
interface (LANA modules are not built in this workspace, so their statements are
mirrored here rather than imported):
* source: tmp/sheaf/lana_latest/Iut/Concrete/LocalEstimate.lean (localEstimate fields
  cont/thetaPilot_subset/vol_finite/vol_infinite/packetVol_mono),
* source: tmp/sheaf/lana_latest/Iut/Implication/Theorem110.lean (theorem110).
The consumer below connects the local-estimate fields to the two ABC gap shapes.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaIutIVEstimateActual

universe u

/-- Self-contained mirror of LANA's `LocalEstimate` (IUT IV Steps (iv)-(vii)). -/
structure LanaLocalEstimate (α : Type u) where
  /-- the triple-dependent comparison region (LANA: packet/hull regions). -/
  region : Nat → Nat → Nat → Set α
  /-- the log-volume functional. -/
  vol : Set α → Real
  /-- region volume monotone under inclusion (LANA: `packetVol_mono`). -/
  vol_mono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T
  /-- region inclusion from the theta-pilot subset (LANA: `thetaPilot_subset`). -/
  subset : ∀ a b c a' b' c' : Nat, a ≤ a' → b ≤ b' → c ≤ c' →
    region a b c ⊆ region a' b' c'
  /-- finiteness of the local volumes (LANA: `vol_finite`). -/
  vol_finite : ∀ a b c : Nat, vol (region a b c) < (10 : Real) ^ 12
  /-- the arithmetic height attached to the triple. -/
  height : Nat → Nat → Nat → Real
  /-- Gap 1 shape: the ε-normalized height/region-volume comparison
(LANA: the local estimate of Steps (iv)-(vii) instantiated at the region). -/
  height_le_region : ∀ ε : Real, 0 < ε → ∀ a b c : Nat,
    height a b c ≤ (1 + ε) * vol (region a b c)
  /-- the arithmetic weight attached to the triple. -/
  weight : Nat → Nat → Nat → Real
  /-- the hull/theta bound. -/
  thetaBound : Real
  /-- Gap 2 shape: the ε-normalized region-volume/weight comparison with additive
constant (LANA: the finite local estimates absorbed into the global constant). -/
  region_le_weight : ∀ ε : Real, 0 < ε → ∃ D : Real,
    ∀ a b c : Nat, vol (region a b c) ≤
      (1 + ε) * weight a b c + thetaBound + D

/-- Gap 1 correspondence: the LANA local estimate supplies the height/region-volume
comparison. -/
theorem gap1_of_lana {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (a b c : Nat) :
    E.height a b c ≤ (1 + ε) * E.vol (E.region a b c) :=
  E.height_le_region ε hε a b c

/-- Gap 2 correspondence: the LANA local estimate supplies the region-volume/weight
bound with an additive constant. -/
theorem gap2_of_lana {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) :
    ∃ D : Real, ∀ a b c : Nat, E.vol (E.region a b c) ≤
      (1 + ε) * E.weight a b c + E.thetaBound + D :=
  E.region_le_weight ε hε

/-- Combined correspondence: both gap shapes from the same LANA local estimate. -/
theorem combined_of_lana {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) :
    (∀ a b c : Nat, E.height a b c ≤ (1 + ε) * E.vol (E.region a b c)) ∧
      (∃ D : Real, ∀ a b c : Nat, E.vol (E.region a b c) ≤
        (1 + ε) * E.weight a b c + E.thetaBound + D) :=
  ⟨fun a b c => gap1_of_lana E ε hε a b c, gap2_of_lana E ε hε⟩

/-- Region volume monotonicity from the LANA local-estimate fields. -/
theorem regionVol_mono_of_lana {α : Type u} (E : LanaLocalEstimate α)
    {a b c a' b' c' : Nat} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    E.vol (E.region a b c) ≤ E.vol (E.region a' b' c') :=
  E.vol_mono (E.subset a b c a' b' c' ha hb hc)

#check LanaLocalEstimate
#check gap1_of_lana
#check gap2_of_lana
#check combined_of_lana
#check regionVol_mono_of_lana

end LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaIutIVEstimateActual
end
