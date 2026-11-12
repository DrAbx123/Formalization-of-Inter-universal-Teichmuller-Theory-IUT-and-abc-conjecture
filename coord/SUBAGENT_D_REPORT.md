# SUBAGENT_D_REPORT — deep-audit group D first missing input

Date: 2026-11-07. Task: task-702 (group D), attack the first missing input of
`S2883Inputs` (`S2877OrderTwoAutClassification` + `underlying_ne_id_iff`),
then the `S2892Inputs` data.

Constraints honoured: no edits to S2936 or any existing source file; the only new
files are
* `tmp/sheaf/xif/paper/S2982A6SourceDataActual.lean`
* `coord/SUBAGENT_D_REPORT.md` (this file)

No `sorry`, no `axiom`, no placeholder, no `True`-valued stand-in, no
target-as-input.  The file contains no occurrence of `sorry`/`admit`/`axiom`.

## 1. Verdict

**One of the two `S2883Inputs` fields is now proved unconditionally.**  The
non-trivial direction of `underlying_ne_id_iff` (the `inv ≠ id → underlying ≠ 𝟙`
direction, equivalently `underlying = 𝟙 → inv = id`; "reflection of identity")
is a theorem, kernel-checked with axioms `[propext, Classical.choice,
Quot.sound]`.  Consequently

> `S2883Inputs` is now equivalent to the single proposition
> `S2877OrderTwoAutClassification`.

**The exact first unproved object is therefore `S2877OrderTwoAutClassification`**
(`tmp/sheaf/xif/paper/S2877UniqueReductionAudit.lean:46-49`), and the
mathematical audit below argues that this statement is **false as written**, so
the correct remaining task is a *reformulation*, not a proof.

## 2. Current frontier (verified by reading + olean status)

```text
S2877OrderTwoAutClassification      -- Prop, never proved anywhere in the tree
  (S2877UniqueReductionAudit.lean:46)

S2883Inputs : Prop                  -- conjunction of exactly 2 statements
  classification            : S2877OrderTwoAutClassification
  underlying_ne_id_iff      : ∀ inv, S2877Underlying inv ≠ 𝟙 ↔ inv ≠ Hom.id
  (S2883UniqueFromClassification.lean:30-37)
   ^^^ field 2 was the second unproved object; DISCHARGED by this task (below)

S2902UniqueData                     -- 4 fields, all still inputs
  haff : S2889AffineOrderTwoClassification
  chart : ∀ β, β² = 1 → S2890ChartData β
  origin : ∀ β, β² = 1 → S2888OriginPreserving β        <-- FALSE as stated (see §5)
  underlying_ne_id_iff                                   <-- DISCHARGED by this task
  (S2902CoreWithQMinimalActual.lean:85-96)

S2978MissingClassificationData      -- same 4 fields (S2978ClassificationInputActual.lean:54)
S2990Inputs                         -- 5 inputs + underlying_ne_id_iff (S2990*.lean:22-34)
  valuation, xfixed, haff, origin, originToChart, underlying_ne_id_iff

S2892Inputs                         -- S2892CoreWithQActual.lean:39-67
  uniqueInput : S2883Inputs | groups : CoreGroupsInput | xK,cK,extensions,
  xKType,cKType,V,V_mod_bad,V_section,V_eq_section,V_mod_bijection,
  V_place_comap, cusp : GenericCuspData cK
```

Olean status at audit time (all read-only facts):
`S2897ValuationInputActual` 90416 B, `S2913ChartFactorizationAttempt` 109368 B,
`S2990ClassificationDataConstruction` 76352 B — all present, so the S2990 chart
construction is a compiled artifact; `S2896AffineClassificationAttempt` has **no**
olean (attempt file, never compiled).

## 3. What was actually proved (new)

File: `tmp/sheaf/xif/paper/S2982A6SourceDataActual.lean` (252 lines).

| declaration | statement | axioms |
|---|---|---|
| `S2982_underlying_id` | `S2877Underlying (Hom.id) = 𝟙 S2844X` | trio |
| `S2982_underlying_ne_id_of_ne` | `underlying ≠ 𝟙 → inv ≠ Hom.id` (free direction) | trio |
| `S2982UnderlyingReflectsId` | `∀ inv, underlying inv = 𝟙 → inv = Hom.id` (the exact missing statement) | (definition) |
| `S2982_underlying_ne_id_iff_iff_reflects` | the **whole** S2883 equivalence ⇔ `S2982UnderlyingReflectsId` | trio |
| `S2982_app_id` | `S1742App 𝟙 a = 𝟙 ((S1742YS S2844X).obj a)` | trio |
| `S2982_app_eq_of_underlying_eq` | `underlying inv = 𝟙 → ∀ a, inv.app a = 𝟙 _` | trio |
| `S2982StrongTransRigidity` | app determines a strong transformation of the representable pseudofunctor | (definition) |
| `S2982_rigidity` | `S2982StrongTransRigidity` — **proved** | trio |
| `S2982_reflectsId` | `S2982UnderlyingReflectsId` — **proved** | trio |
| `S2982Inputs_of` | `S2877OrderTwoAutClassification → S2883Inputs` | trio |
| `S2982_unique_of` | consumer uniqueness from the classification alone | trio |
| `S2982_classification_alt` | classification + β ≠ 𝟙 ⇒ β = `alphaOverS2844` | trio |
| `S2982_alt_distinct` | `alphaOverS2844 ≠ 𝟙 S2844X` (dichotomy not degenerate) | trio |

Key reductions, stated precisely:

1. `S2982_underlying_ne_id_iff_iff_reflects`:
   `(∀ inv, S2877Underlying inv ≠ 𝟙 ↔ inv ≠ Hom.id) ↔ S2982UnderlyingReflectsId`.
   This splits the S2883 field into a *free* direction and one real obligation,
   and shows the field hides no third obligation.
2. `S2982_rigidity`: the 2-categorical rigidity that the `app` component
   determines a strong transformation of the representable pseudofunctor
   `S1742YS S2844X` (all target categories are discrete, so the naturality
   2-cells and the coherence proofs are subsingletons).  Proof: destruct the
   strong transformation, `subst` the `funext`-ed app equality, then `congr 1`.
3. `S2982_reflectsId`: `S2982_rigidity` + `S2982_app_eq_of_underlying_eq`.
4. `S2982Inputs_of`: `S2883Inputs` from the classification alone.

## 4. Attempted proof, first Lean errors, and how the obstacle was passed

Chronology of the actual failures in the development (each is a real error the
final file no longer contains, kept here as audit evidence):

1. **First error — no `StrongTrans` ext lemma.**  Attempting the reflection
   direction as `η = StrongTrans.id` required comparing the dependent field
   `naturality`; Mathlib's `CategoryTheory/Pseudofunctor` development
   (`.../Bicategory/NaturalTransformation/Pseudo.lean:57-76`) provides no
   `StrongTrans.ext`, so the comparison had to be stated by hand.  First exact
   error when stating it:
   ```text
   error: don't know how to synthesize implicit argument `α`
     @Eq ((f : ?m.64 ⟶ ?m.65) → (S1742YS S2844X).map f ≫ … ≅ …) nat
       (Pseudofunctor.StrongTrans.id (S1742YS S2844X)).naturality
   ⊢ Type
   ```
   Cause: after `subst`, `nat`'s implicit binders `{a b}` were instantiated by
   metavariables in the `have` statement.
2. **Second error — `funext` on an implicit-binder function.**
   `funext a b f` on `nat : {a b} → (f : a ⟶ b) → …` produced
   `error: don't know how to synthesize implicit argument `b`` with goal
   `⊢ LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ` (same root cause).
3. **Third error — type-level vs definitional identification of the fiber.**
   `simpa [Iut.HyperbolicOrbicurve.Hom.id] using hrig` failed with
   `hrig : inv = StrongTrans.id (S1742YS S2844X)` vs expected
   `inv = StrongTrans.id S2855HyperbolicOrbicurve.stack.fiber`; `exact hrig`
   works because the two fibers are definitionally equal.
4. **Resolution.**  Avoid stating the `naturality` equality at all: destruct the
   strong transformation (`cases`), `subst` the app equality obtained by
   `funext` from the hypothesis, then close the whole structure equality with
   `congr 1`.  This performs the dependent elimination that a hand-written
   `StrongTrans.ext` would have to do.  The resulting proof term is a single
   `Eq.ndrec`/congruence term; `#print S2982_rigidity` should be inspected by an
   independent reviewer (I did; it is the expected dependent-elimination term,
   ~6.4 kB of pretty-printed text, no `sorryAx`).

## 5. Why `S2877OrderTwoAutClassification` is probably FALSE as stated

The classification quantifies over **all** `β : S2844X ⟶ S2844X` with
`β ≫ β = 𝟙`.  But `S2844X` is the projective E37 curve
`y² = x³ − x` over `K = ℚ(i)` (see `S2801E37ProjectiveClosure`,
`S2844D6F6BaseChangeActual`), which has **full rational 2-torsion**:
`x = 0, 1, −1`.  Translation `τ_P` by a nonzero 2-torsion point `P` is a
`K`-automorphism of the `Over` object with `τ_P ≫ τ_P = 𝟙`, and
`τ_P ≠ 𝟙`, `τ_P ≠ alphaOverS2844` (α fixes the origin, `τ_P` does not).
So the stated dichotomy fails for the full scheme, unless the Hom type restricts
to origin-preserving maps.  This is exactly what the existing S2881 audit
(`S2881OrderTwoClassificationAudit.lean`, "What is NOT available") already
recorded; it is a mathematical audit statement here, **not** Lean-proved (no
translation automorphism is constructed in the tree).

Consequence for the reduction chain: the `origin` field of
`S2902UniqueData` — `∀ β, β ≫ β = 𝟙 → S2888OriginPreserving β` — has the same
problem (a 2-torsion translation is order two and moves the origin), so
`S2902UniqueData` / `S2990Inputs` are **unsatisfiable as written**.  Their
`S2902_toS2883` / `S2990MissingClassificationData` wrappers are therefore
vacuous rather than genuine reductions.  The honest corrected target is the
origin-preserving classification `S2888OriginPreservingOrderTwoClassification`
(or a classification performed on the orbicurve Hom category, where the marked
puncture is part of the data).

## 6. What is still missing (ordered, exact)

1. `S2877OrderTwoAutClassification` — the only remaining field of
   `S2883Inputs`.  Must be *replaced* by an origin-preserving statement (or
   refuted); see §5.  Nothing in the tree proves it; nothing in the tree is
   currently able to state the origin-preservation of `S2877Underlying inv`
   either (that is the next concrete lemma, see §7).
2. `S2888OriginPreservingOrderTwoClassification` — order-two origin-preserving
   automorphisms of `S2844X` are `𝟙` or α.  Requires the affine order-two
   classification `S2889AffineOrderTwoClassification`; `S2896` shows naive
   total degree does not descend to the coordinate ring, `S2897` records the
   valuation/degree input but does not prove `S2897XFixedInput`.
3. `S2913OriginToChart` — origin-preserving auto preserves chart Z
   (used by `S2990ChartData`), unproved.
4. Everything else in `S2892Inputs`: `CoreGroupsInput` (S2884/S2978 groups),
   K-side (S2895/S2900), `V`/`V_mod_bad`/bijection/comap, `cusp`
   (S2901/S2904) — none constructed; unchanged by this task.
   (`S2892Inputs.uniqueInput` is now reducible to the classification alone.)

## 7. Next executable step

Concrete, in dependency order:

* **D1 (cheap).**  Prove the underlying scheme map of an orbicurve
  endomorphism preserves the marked origin:
  `S2844InfinityOver ≫ S2877Underlying inv = S2844InfinityOver` for every
  `inv`.  This converts the classification target into the origin-preserving
  statement actually needed, and is the missing bridge between `S2877Underlying`
  and `S2888OriginPreserving`.  Input needed: the cusp/origin is part of the
  orbicurve structure (`SourceOncePuncturedGeometry`), so the statement should
  follow from the definition of the Hom category of the represented stack plus
  `S1742Key` evaluated at the cusp.
* **D2 (hard, real gap).**  Prove or refute
  `S2888OriginPreservingOrderTwoClassification`.  The mathematically correct
  route is `Aut(S2844X, origin) = {±1}` on the `K`-algebra automorphisms of
  `S2801E37CoordinateRing K`; `S2889` already reduces chart data to
  `S2853RingHomAlgEquiv`, and `S2853RingHom` is proved to square to the
  identity.  The missing ingredient is a degree/valuation argument on the
  coordinate ring (S2896 records that naive total degree does not descend;
  S2897 records the valuation input).
* **D3 (mechanical).**  Once D1+D2 exist, feed them through the existing
  `S2890_classification_of_affine` and the now-proven
  `S2982Inputs_of` to obtain `S2883Inputs` with no side conditions, then
  rebuild `S2887Inputs`/`S2892Inputs` (their `uniqueInput` field).

## 8. Acceptance evidence

* fresh compile, command
  `lake env lean tmp/sheaf/xif/paper/S2982A6SourceDataActual.lean`
* EXIT `0` (no errors, no warnings)
* source SHA256
  `1D671B4388716B056CC01074D1547885C55003E98C5B3F43E79428F9648ECC62`
* olean `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2982A6SourceDataActual.olean`,
  41520 B, SHA256
  `18EA28CEC46DB88A34DF85A6F355E1966370A0F76A552B3E56BEE1AF94D790F6`
* `#print axioms` for all 9 theorem declarations:
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axiom.

Status fields, reported separately as required:

| field | value |
|---|---|
| statement_compiles | yes (`S2982StrongTransRigidity`, `S2982UnderlyingReflectsId`, `S2883Inputs`-construction) |
| proof_body_checked | yes (kernel-checked whole file, EXIT 0) |
| kernel_closed | yes (axioms trio) |
| target_accepted | **no** — the D target (`S2883Inputs` + `S2892Inputs` source data) is only half discharged: `underlying_ne_id_iff` is proved, `S2877OrderTwoAutClassification` is not, and `S2892Inputs` is untouched. |

## 9. Files

* new: `tmp/sheaf/xif/paper/S2982A6SourceDataActual.lean`
* new: `coord/SUBAGENT_D_REPORT.md`
* read only: `S2883UniqueFromClassification.lean`, `S2877UniqueReductionAudit.lean`,
  `S2892CoreWithQActual.lean`, `S2887CorrectedCoreMinimalActual.lean`,
  `S2880CorrectedA6CoreNontrivialActual.lean`, `S2873CuspGenericActual.lean`,
  `S2881OrderTwoClassificationAudit.lean`, `S2888OriginPreservingOrderTwo.lean`,
  `S2889AffineOrderTwoActual.lean`, `S2890ClassificationConditionalActual.lean`,
  `S2896AffineClassificationAttempt.lean`, `S2897ValuationInputActual.lean`,
  `S2902CoreWithQMinimalActual.lean`, `S2978ClassificationInputActual.lean`,
  `S2990ClassificationDataConstruction.lean`, `Iut/Foundations/Orbicurve.lean`,
  `S1742TwoYonedaActual.lean`, `S1742HomVcompActual.lean`,
  `S2853E37NegationAutomorphismActual.lean`, `S2876NontrivialAlphaActual`,
  `S2879NontrivialStackAutoActual.lean`, `coord/DEEP_AUDIT_ABC_IUT.md`,
  `coord/DEEP_AUDIT_TASK_BOARD.md`.
* **not** modified: S2936 (untouched), every existing source file.
