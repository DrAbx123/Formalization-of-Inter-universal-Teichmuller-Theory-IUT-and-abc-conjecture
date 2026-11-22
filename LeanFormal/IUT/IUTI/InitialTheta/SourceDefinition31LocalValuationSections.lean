import LeanFormal.IUT.IUTI.InitialTheta.SourceArithmeticPrelude
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# Definition 3.1(e): the place-section layer of the D7 clause

Frozen scope (2026-10-16, `estimates-rec8` D3.1 item 21, D5-D9 menu).
Corpus anchor: IUT I, Definition 3.1(e): "V ... is a subset that induces
a natural bijection V ~> V_mod -- i.e., a section of the natural
surjection V(K) ->> V_mod" (text-extraction lines 3216-3220 of IUT I).

What is constructed here, for every arithmetic input `A`:

* the selected upstairs carrier `V` as the image of the canonical
  restriction section of `K/F_mod` (`SourceArithmeticPrelude.canonical`);
* the natural map `V -> V_mod` (restriction) and its section
  `V_mod -> V` (extension), with both round trips;
* kind preservation along the section: `IsFinite`/`IsInfinite` are
  invariant, hence `V_non` and `V_mod_non`, resp. `V_arc` and `V_mod_arc`,
  are equivalent as subtypes;
* the packaged six-slot layer `SourceValuationSectionLayer` with a
  canonical instance for every `A`, matching the section-map slots of
  `SourceSectionClause` (`SourceDefinition31Boundary.lean`:514-535).

What is deliberately NOT constructed here (named residual):

* the local-group slots (`localGroupCarrier`,
  `modifiedLocalGroupCarrier`, the pointwise bijective
  `localGroupSection`, i.e. the paper's Pi_Xv inside Pi_Cv content),
  which need actual orbicurves and their etale fundamental groups
  (the open D6 construction);
* the `finitePlaceData`/`infinitePlaceData` proposition content of the
  clause (good/bad refinements and their source conditions), and the
  base-change clauses attached to (e);
* valuation-value-level compatibility (`adicAbv`): assessed and not
  stated here; Mathlib has no comap/section compatibility lemma for
  `NumberField.adicAbv`.

Honest labels.  The paper treats `V` as part of the initial Theta-data
(input).  This file constructs one canonical admissible `V` from the
arithmetic base, exactly as `SourceArithmeticPrelude` does for the
restriction section; it does not claim that every source `V` arises this
way, and it does not close `D7SectionConstruction`
(`SourceDefinition31RootLemmas.lean`:5164), whose local-group half is
open.

Redundancy notes.  `valuationSectionMap_eq_comap` and
`valuationSectionRightInverse_apply` restate
`SourceArithmeticPrelude.selectedEquiv_symm_apply` / `selectedEquiv_apply`
in layer vocabulary; the two round trips restate the `selectedEquiv`
inverse laws.  They are kept so consumers can use the clause-slot shape
without unfolding the `Equiv`.
-/

namespace LeanFormal.IUT

noncomputable section

universe u v

namespace InitialThetaSource

/-! ## Generic place lemmas used by the layer -/

/-- Restriction of places preserves the finite kind, for arbitrary number
field extensions.  (No such lemma was present in
`Foundations.NumberField.Places`; it is stated under this task's
single-new-file constraint.) -/
theorem comap_place_isFinite_iff {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (place : NumberFieldPlace K) :
    NumberFieldPlace.IsFinite (NumberFieldPlace.comap (k := k) place) ↔
      NumberFieldPlace.IsFinite place := by
  cases place with
  | finite p => simp
  | infinite p => simp

/-- Restriction of places preserves the infinite kind (same provenance
note as `comap_place_isFinite_iff`). -/
theorem comap_place_isInfinite_iff {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (place : NumberFieldPlace K) :
    NumberFieldPlace.IsInfinite (NumberFieldPlace.comap (k := k) place) ↔
      NumberFieldPlace.IsInfinite place := by
  cases place with
  | finite p => simp
  | infinite p => simp

/-- The natural restriction of places is surjective: lying over for
finite places, extension of complex embeddings for infinite places. -/
theorem comap_place_surjective {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] :
    Function.Surjective (NumberFieldPlace.comap (k := k) :
      NumberFieldPlace K → NumberFieldPlace k) := by
  intro w
  cases w with
  | finite p =>
      exact ⟨NumberFieldPlace.finite
        (NumberFieldPlace.finiteLift (K := K) p), by simp⟩
  | infinite p =>
      exact ⟨NumberFieldPlace.infinite
        (NumberFieldPlace.infiniteLift (K := K) p), by simp⟩

/-! ## The layer carried by a chosen place section -/

section Layer

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- The upstairs valuation carrier `V` of Definition 3.1(e) carried by a
place section: the selected set of places of `K`. -/
abbrev valuationSectionCarrier (P : SourceArithmeticPrelude A) : Type u :=
  {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces}

/-- The modified (downstairs) valuation carrier `V_mod` of Definition
3.1(e): the place carrier of the modification field `F_mod`. -/
abbrev modifiedValuationSectionCarrier (A : InitialThetaArithmeticData.{u} l) : Type u :=
  NumberFieldPlace A.Fmod

/-- The natural restriction map `V -> V_mod` of Definition 3.1(e). -/
noncomputable def valuationSectionMap (P : SourceArithmeticPrelude A) :
    valuationSectionCarrier P → modifiedValuationSectionCarrier A :=
  fun v => P.selectedEquiv.symm v

/-- The section `V_mod -> V` of the natural restriction: the extension
chosen per modified place. -/
noncomputable def valuationSectionRightInverse (P : SourceArithmeticPrelude A) :
    modifiedValuationSectionCarrier A → valuationSectionCarrier P :=
  fun w => P.selectedEquiv w

theorem valuationSectionMap_eq_comap (P : SourceArithmeticPrelude A)
    (v : valuationSectionCarrier P) :
    valuationSectionMap P v = NumberFieldPlace.comap (k := A.Fmod) v.1 :=
  P.selectedEquiv_symm_apply v

theorem valuationSectionRightInverse_apply (P : SourceArithmeticPrelude A)
    (w : modifiedValuationSectionCarrier A) :
    (valuationSectionRightInverse P w).1 = P.placeSection.lift w :=
  P.selectedEquiv_apply w

/-- Round trip `V -> V_mod -> V`: the extension of the restriction of a
selected place is the place itself.  This is the `lift(comap v) = v` half
of Definition 3.1(e)'s section property. -/
theorem valuationSectionRightInverse_map (P : SourceArithmeticPrelude A)
    (v : valuationSectionCarrier P) :
    valuationSectionRightInverse P (valuationSectionMap P v) = v :=
  P.selectedEquiv_right_inverse v

/-- Round trip `V_mod -> V -> V_mod`: the restriction of the extension is
the original place.  This is the `comap(lift w) = w` half. -/
theorem valuationSectionMap_rightInverse (P : SourceArithmeticPrelude A)
    (w : modifiedValuationSectionCarrier A) :
    valuationSectionMap P (valuationSectionRightInverse P w) = w :=
  P.selectedEquiv_left_inverse w

/-- The round trip in restriction form: `comap(lift w) = w` for the
chosen extension. -/
theorem valuationSectionRightInverse_comap (P : SourceArithmeticPrelude A)
    (w : modifiedValuationSectionCarrier A) :
    NumberFieldPlace.comap (k := A.Fmod)
      (valuationSectionRightInverse P w).1 = w :=
  P.placeSection.comap_lift w

theorem valuationSectionMap_bijective (P : SourceArithmeticPrelude A) :
    Function.Bijective (valuationSectionMap P) :=
  P.selectedEquiv.symm.bijective

theorem valuationSectionRightInverse_bijective (P : SourceArithmeticPrelude A) :
    Function.Bijective (valuationSectionRightInverse P) :=
  P.selectedEquiv.bijective

/-- Kind preservation for the restriction: a selected place `v` is
nonarchimedean exactly when its restriction to `F_mod` is. -/
theorem valuationSectionMap_isFinite_iff (P : SourceArithmeticPrelude A)
    (v : valuationSectionCarrier P) :
    NumberFieldPlace.IsFinite (valuationSectionMap P v) ↔
      NumberFieldPlace.IsFinite v.1 := by
  rw [valuationSectionMap_eq_comap P v]
  exact comap_place_isFinite_iff (k := A.Fmod) v.1

/-- Kind preservation for the restriction, archimedean case. -/
theorem valuationSectionMap_isInfinite_iff (P : SourceArithmeticPrelude A)
    (v : valuationSectionCarrier P) :
    NumberFieldPlace.IsInfinite (valuationSectionMap P v) ↔
      NumberFieldPlace.IsInfinite v.1 := by
  rw [valuationSectionMap_eq_comap P v]
  exact comap_place_isInfinite_iff (k := A.Fmod) v.1

/-- Kind preservation for the extension, nonarchimedean case. -/
theorem valuationSectionRightInverse_isFinite_iff
    (P : SourceArithmeticPrelude A) (w : modifiedValuationSectionCarrier A) :
    NumberFieldPlace.IsFinite (valuationSectionRightInverse P w).1 ↔
      NumberFieldPlace.IsFinite w := by
  rw [valuationSectionRightInverse_apply P w]
  have h := comap_place_isFinite_iff (k := A.Fmod) (K := A.K)
    (P.placeSection.lift w)
  rw [P.placeSection.comap_lift w] at h
  exact h.symm

/-- Kind preservation for the extension, archimedean case. -/
theorem valuationSectionRightInverse_isInfinite_iff
    (P : SourceArithmeticPrelude A) (w : modifiedValuationSectionCarrier A) :
    NumberFieldPlace.IsInfinite (valuationSectionRightInverse P w).1 ↔
      NumberFieldPlace.IsInfinite w := by
  rw [valuationSectionRightInverse_apply P w]
  have h := comap_place_isInfinite_iff (k := A.Fmod) (K := A.K)
    (P.placeSection.lift w)
  rw [P.placeSection.comap_lift w] at h
  exact h.symm

/-- The nonarchimedean slice equivalence `V_mod_non -> V_non` of
Definition 3.1(e): a modified place is finite exactly when its selected
extension is. -/
noncomputable def finiteValuationSectionEquiv (P : SourceArithmeticPrelude A) :
    {w : modifiedValuationSectionCarrier A //
      NumberFieldPlace.IsFinite w} ≃
      {v : valuationSectionCarrier P //
        NumberFieldPlace.IsFinite v.1} where
  toFun w :=
    ⟨valuationSectionRightInverse P w.1,
      (valuationSectionRightInverse_isFinite_iff P w.1).mpr w.2⟩
  invFun v :=
    ⟨valuationSectionMap P v.1,
      (valuationSectionRightInverse_isFinite_iff P
        (valuationSectionMap P v.1)).mp
        (by
          have h := congrArg
            (fun x : valuationSectionCarrier P =>
              NumberFieldPlace.IsFinite x.1)
            (valuationSectionRightInverse_map P v.1)
          exact h.symm ▸ v.2)⟩
  left_inv w := Subtype.ext (valuationSectionMap_rightInverse P w.1)
  right_inv v := Subtype.ext (valuationSectionRightInverse_map P v.1)

/-- The archimedean slice equivalence `V_mod_arc -> V_arc` of Definition
3.1(e). -/
noncomputable def infiniteValuationSectionEquiv (P : SourceArithmeticPrelude A) :
    {w : modifiedValuationSectionCarrier A //
      NumberFieldPlace.IsInfinite w} ≃
      {v : valuationSectionCarrier P //
        NumberFieldPlace.IsInfinite v.1} where
  toFun w :=
    ⟨valuationSectionRightInverse P w.1,
      (valuationSectionRightInverse_isInfinite_iff P w.1).mpr w.2⟩
  invFun v :=
    ⟨valuationSectionMap P v.1,
      (valuationSectionRightInverse_isInfinite_iff P
        (valuationSectionMap P v.1)).mp
        (by
          have h := congrArg
            (fun x : valuationSectionCarrier P =>
              NumberFieldPlace.IsInfinite x.1)
            (valuationSectionRightInverse_map P v.1)
          exact h.symm ▸ v.2)⟩
  left_inv w := Subtype.ext (valuationSectionMap_rightInverse P w.1)
  right_inv v := Subtype.ext (valuationSectionRightInverse_map P v.1)

end Layer

/-! ## The packaged place-section layer -/

section PackagedLayer

variable {l : PrimeGeFive}

/-- The place-section half of the D7 clause (Definition 3.1(e)): the
carriers `V`, `V_mod`, the natural bijection `V -> V_mod` and its section
`V_mod -> V`, with both round trips.  The fields match the slots
`valuationCarrier`, `modifiedValuationCarrier`, `sectionMap`,
`sectionRightInverse`, `section_left_inverse`, `section_right_inverse` of
`SourceSectionClause` (`SourceDefinition31Boundary.lean`:514-535); the
local-group and place-data slots are deliberately absent. -/
structure SourceValuationSectionLayer
    (A : InitialThetaArithmeticData.{u} l) where
  valuationCarrier : Type u
  modifiedValuationCarrier : Type u
  sectionMap : valuationCarrier → modifiedValuationCarrier
  sectionRightInverse : modifiedValuationCarrier → valuationCarrier
  section_left_inverse : ∀ x, sectionRightInverse (sectionMap x) = x
  section_right_inverse : ∀ y, sectionMap (sectionRightInverse y) = y

namespace SourceValuationSectionLayer

/-- The layer carried by an arbitrary chosen restriction section. -/
noncomputable def ofPrelude {A : InitialThetaArithmeticData.{u} l}
    (P : SourceArithmeticPrelude A) :
    SourceValuationSectionLayer A where
  valuationCarrier := valuationSectionCarrier P
  modifiedValuationCarrier := modifiedValuationSectionCarrier A
  sectionMap := valuationSectionMap P
  sectionRightInverse := valuationSectionRightInverse P
  section_left_inverse := valuationSectionRightInverse_map P
  section_right_inverse := valuationSectionMap_rightInverse P

/-- The canonical layer carried by the canonical restriction section of
the arithmetic input. -/
noncomputable def canonical (A : InitialThetaArithmeticData.{u} l) :
    SourceValuationSectionLayer A :=
  ofPrelude (SourceArithmeticPrelude.canonical A)

theorem nonempty_canonical (A : InitialThetaArithmeticData.{u} l) :
    Nonempty (SourceValuationSectionLayer A) :=
  ⟨canonical A⟩

theorem exists_canonical (l : PrimeGeFive) :
    ∀ A : InitialThetaArithmeticData.{u} l,
      Nonempty (SourceValuationSectionLayer A) :=
  fun A => nonempty_canonical A

end SourceValuationSectionLayer

end PackagedLayer

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Supply card: the place-section layer of Definition 3.1(e) for the D7
clause, constructed for every arithmetic input. -/
def definition31LocalValuationSectionLayer : Obligation :=
  { id := "IUT-I.definition-3.1-D7-place-section-layer"
    source := "IUT I, Definition 3.1(e) (extraction lines 3216-3220)"
    status := VerificationStatus.provedKernel
    note :=
      "D7 (e) place-section half, unconditional in the arithmetic input. " ++
        "For every A, SourceValuationSectionLayer.canonical constructs the " ++
        "selected carrier V as the image of the canonical restriction " ++
        "section K/F_mod (SourceArithmeticPrelude.canonical), the natural " ++
        "bijection V -> V_mod (valuationSectionMap, " ++
        "valuationSectionRightInverse) with both round trips " ++
        "(valuationSectionRightInverse_map, valuationSectionMap_rightInverse), " ++
        "and the kind-preserving slice equivalences " ++
        "finiteValuationSectionEquiv / infiniteValuationSectionEquiv " ++
        "(via comap_place_isFinite_iff / comap_place_isInfinite_iff and " ++
        "comap_place_surjective). The carrier pair is exactly the " ++
        "section-map slot group of SourceSectionClause " ++
        "(SourceDefinition31Boundary:514-535). The paper's V is initial " ++
        "Theta-data input; this is one canonical admissible choice, not a " ++
        "classification, and not a closure of the D7 gate " ++
        "D7SectionConstruction (SourceDefinition31RootLemmas:5164). The " ++
        "local-group and place-data slots are NOT supplied; see " ++
        "definition31LocalGroupSectionResidual."
    dependsOn :=
      [ "IUT-I.definition-3.1-A2-arithmetic-prelude",
        "Foundations.NumberField.places" ] }

/-- Residual card: the local-group half of Definition 3.1(e) remains
open. -/
def definition31LocalGroupSectionResidual : Obligation :=
  { id := "IUT-I.definition-3.1-D7-local-group-residual"
    source := "IUT I, Definition 3.1(e) (extraction lines 3220-3272)"
    status := VerificationStatus.pending
    note :=
      "D7 (e) local-group half. Slots remaining unfilled by the " ++
        "place-section layer: localGroupCarrier/modifiedLocalGroupCarrier " ++
        "(a family Pi_Xv / Pi_Cv over V), the pointwise bijective " ++
        "localGroupSection (the Pi_Xv inside Pi_Cv content from the " ++
        "cartesian diagram of etale coverings), the " ++
        "finitePlaceData/infinitePlaceData propositions, and the " ++
        "V_good/V_bad refinement with the base-change clauses. These need " ++
        "actual orbicurves X_K, C_K and their etale fundamental groups, " ++
        "i.e. the D6 construction (d6_status, SourceDefinition31RootLemmas" ++
        ":5303), which is open: no tree supplier constructs an actual " ++
        "orbicurve over K from A alone (SourceClauseConstructors supplies " ++
        "conditional constructors that take the geometric objects as " ++
        "hypotheses). A second source line " ++
        "(SourceDefinition31Quantifiers:566, SourceSignQuotientData) " ++
        "carries V_section/V_mod_bijection as supplied source fields of a " ++
        "datum that also contains the orbicurve family; it is conditional " ++
        "and does not fill the D7 gate. Valuation-value compatibility " ++
        "(adicAbv) was assessed and is not stated: Mathlib has no " ++
        "comap/section lemma for NumberField.adicAbv."
    dependsOn :=
      [ "IUT-I.definition-3.1-D7-place-section-layer",
        "IUT-I.definition-3.1-D6" ] }

end LeanFormal.IUT.Audit
