/-
# S1866: apex coherence for the coherent covers --- reduction, no-go, and the exact first missing

## Target

S1854/S1856 left the exact first missing for pullbacks and finite coproducts on the
coherent category as

  `S1854PullbackApexCoherent h` :
    for every cospan of underlying covers of coherent covers, the chosen
    `Limits.pullback f g` is the underlying cover of some coherent cover;

  `S1854CoproductApexCoherent h0 h2` :
    the chosen initial object `⊥_ S1728Cover` and every chosen binary coproduct
    `A.cover ⨿ B.cover` of coherent covers are underlying covers of coherent covers.

The task was to prove these from S1852's coherent-cover datum together with
S1832/S1833's limit and coproduct structures, or to isolate the exact first missing.

## Verdict

They are **not** proved here.  The obstruction is not a missing category-theoretic
transport: S1856 already proves that full-and-faithful reflection transports the
S1728 limits/colimits once the apex covers are coherent.  The obstruction is the
object-level presentation datum:

* a cover is a *recorded* weak finite-etale structure (`OrbicurveFiniteEtaleCover` =
  source stack + structure map + `EtaleStackFiniteEtaleMorphism`), and coherence is a
  property of that recorded presentation, not of the underlying stack map;
* the S1728 pullback/coproduct apex is an opaque choice inside the Prop-valued
  `HasPullbacks` / `HasInitial` / `HasBinaryCoproducts` fields, and the universal
  property determines it only up to isomorphism of covers;
* coherence is not invariant under isomorphism of covers.  This is proved
  concretely below: the terminal cover `S1762TerminalCover` is coherent, the doubled
  cover `S1850DoubledCover` is not, the two have the *same* source and structure map
  and are isomorphic in `S1728Cover` (`S1866TerminalDoubled_iso`), and the same
  identity cospan admits two `S1832TwoPullback` data with these two apexes
  (`S1866TwoPullbackApexNotDetermined`).  Consequently no argument from the
  universal property of the fibre product alone can force the chosen apex
  presentation to be strong, and the natural but false assertion "every
  two-pullback apex is coherent" is refuted (`S1866TwoPullbackApexAllStrong_false`).

## What is proved here

1. `S1866StrongCoverOf Y`: the exact presentation-level condition on a recorded
   cover `Y` --- its recorded weak finite-etale structure admits a strong refinement
   with the *same* base-change presentations.  Equivalently, every recorded
   base-change square of `Y` satisfies `S1852ConeEssSurj` (`..._iff_baseChange`),
   equivalently `Y` is the underlying cover of a coherent cover
   (`..._iff_coherent`).

2. The exact first missing for pullbacks, `S1866PullbackApexFirstMissing h`: every
   recorded base-change square of the chosen `Limits.pullback f g` carries
   `S1852ConeEssSurj`, for every cospan of coherent covers.  It is proved equivalent
   to `S1854PullbackApexCoherent h`; this equivalence is the precise statement that
   the missing input is exactly the strongness of the chosen apex presentations.

3. The same for finite coproducts (`S1866CoproductApexFirstMissing h0 h2`), with a
   specialization to S1833's affine equivalence
   (`S1866CoproductApexFirstMissingAffine`).

4. Non-vacuity and the no-go: the terminal cover is strong, the doubled cover is
   not, the two have the same source and structure map, and they are isomorphic as
   recorded covers; the S1832 fibre-product data therefore do not determine the
   coherence of their apex.

5. The first missing is connected back to S1856's named statements
   (`S1866PullbackFirstMissing_iff`, `S1866CoproductFirstMissing_iff`), and the
   consumers `S1856HasPullbacks` / `S1856HasFiniteCoproducts` are re-exported from
   the presentation-level form, at both hom universes: `S1866HasPullbacks`,
   `S1866HasFiniteCoproducts` at `Category.{1,1}`, and
   `S1866HasPullbacks01`, `S1866HasInitial01`, `S1866HasBinaryCoproducts01`,
   `S1866HasFiniteCoproducts01` at the target universe `Category.{0,1}` (via S1857).

## Honest boundary

* `S1854PullbackApexCoherent` and `S1854CoproductApexCoherent` are not inhabited in
  this file; the first-missing predicates are plain `Prop`s with no inhabitant.  No
  fake coherent cover, strong presentation or limit is produced.
* The no-go statements do not assert that the geometric fibre product of two
  coherent covers is non-coherent.  They show that the recorded presentation of the
  chosen apex is the load-bearing datum: a genuine construction of the fibre product
  (and of the coproducts) together with its strong presentations is required.
* No sorry, no new axiom.  Only `propext`, `Classical.choice` and `Quot.sound`
  occur; see the audit block.
-/

import tmp.sheaf.xif.paper.S1856CoherentLimitsActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1833ActualCoverCoproductsActual
import tmp.sheaf.xif.paper.S1857CoherentLimits01Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1866ApexCoherenceActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual

/-! ## 1. The strong-presentation condition on a recorded cover -/

/-- **The presentation-level coherence condition on a recorded cover.**  The recorded
weak finite-etale structure `Y.finiteEtale` admits a strong refinement with exactly
the same base-change presentations.  This is the condition that the *chosen* cover
presentation is coherent, as opposed to the weaker condition that some isomorphic
cover is coherent. -/
def S1866StrongCoverOf (Y : S1728Cover) : Prop :=
  ∃ M : StrongEtaleStackFiniteEtaleMorphism Y.map, M.toWeak = Y.finiteEtale

/-- **The condition is literally the strongness of every recorded base change.** -/
theorem S1866StrongCoverOf_iff_baseChange (Y : S1728Cover) :
    S1866StrongCoverOf Y ↔
      ∀ (T : SchemeOverField S1726K)
        (q : Pseudofunctor.StrongTrans
          (schemeRepresentableEtalePseudofunctor S1726K T)
          S1726Orbicurve.stack.fiber),
        S1852ConeEssSurj (Y.finiteEtale.baseChange T q) := by
  constructor
  · rintro ⟨M, hM⟩ T q
    rw [← hM]
    change S1852ConeEssSurj (M.baseChange T q).toWeak
    exact (M.baseChange T q).coneEssSurj
  · intro h
    let M : StrongEtaleStackFiniteEtaleMorphism Y.map :=
      { baseChange := fun T q => ⟨Y.finiteEtale.baseChange T q, h T q⟩
        hasProperty := fun T q => Y.finiteEtale.hasProperty T q }
    exact ⟨M, rfl⟩

/-- **The condition is equivalent to being the underlying cover of a coherent
cover**, with the same recorded cover structure on the nose. -/
theorem S1866StrongCoverOf_iff_coherent (Y : S1728Cover) :
    S1866StrongCoverOf Y ↔ ∃ C : CoherentCover, C.cover = Y := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨src, mp, fe⟩ := Y
    refine ⟨CoherentCover.ofStrong
      { source := src, map := mp, finiteEtale := M }, ?_⟩
    change (⟨src, mp, M.toWeak⟩ : S1728Cover) = ⟨src, mp, fe⟩
    rw [hM]
  · rintro ⟨C, hC⟩
    subst hC
    exact ⟨C.toStrongCover.finiteEtale, rfl⟩

/-- The terminal (identity) cover carries the strong identity-point structure at
every test point; its recorded weak presentation is the canonical one. -/
theorem S1866StrongCoverOf_terminal : S1866StrongCoverOf S1762TerminalCover :=
  ⟨S1854StrongOfS1762, rfl⟩

/-- **The doubled cover is not strong**: no strong structure forgets to its recorded
doubled presentation (S1852). -/
theorem S1866StrongCoverOf_doubled_not : ¬ S1866StrongCoverOf S1850DoubledCover := by
  rintro ⟨M, hM⟩
  exact S1852Doubled_not_strong ⟨M, hM⟩

/-- **Same source and structure map, different coherence.**  The terminal and the
doubled cover are two recorded covers with identical source stack and structure map;
the first is strong, the second is not.  Coherence is therefore a property of the
recorded presentation, not of the underlying stack map. -/
theorem S1866SameSourceMap_differentStrength :
    S1762TerminalCover.source = S1850DoubledCover.source ∧
      S1762TerminalCover.map = S1850DoubledCover.map ∧
      S1866StrongCoverOf S1762TerminalCover ∧
      ¬ S1866StrongCoverOf S1850DoubledCover :=
  ⟨rfl, rfl, S1866StrongCoverOf_terminal, S1866StrongCoverOf_doubled_not⟩

/-! ## 2. Coherence is not invariant under isomorphism of recorded covers -/

/-- The identity cover map of the terminal cover, the cospan used below. -/
abbrev S1866IdentityCoverMap : S1728CoverMap S1762TerminalCover S1762TerminalCover :=
  S1641CoverMapId S1762TerminalCover

/-- The identity map of the common source, as a cover map from the terminal cover to
the doubled cover. -/
noncomputable def S1866TerminalToDoubled :
    S1728CoverMap S1762TerminalCover S1850DoubledCover where
  map := Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber
  commutes := (S1641CoverMapId S1762TerminalCover).commutes

/-- The same identity map, as a cover map from the doubled cover to the terminal
cover. -/
noncomputable def S1866DoubledToTerminal :
    S1728CoverMap S1850DoubledCover S1762TerminalCover where
  map := Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber
  commutes := (S1641CoverMapId S1762TerminalCover).commutes

/-- **The terminal and the doubled cover are isomorphic in the S1728 cover
category.**  The isomorphism is the identity on the common source; only the recorded
weak finite-etale data differ. -/
theorem S1866TerminalDoubled_iso :
    Nonempty (S1762TerminalCover ≅ S1850DoubledCover) := by
  refine ⟨?_⟩
  refine ⟨S1832Q S1866TerminalToDoubled, S1832Q S1866DoubledToTerminal, ?_, ?_⟩
  · show S1832Q S1866TerminalToDoubled ≫ S1832Q S1866DoubledToTerminal =
      𝟙 S1762TerminalCover
    rw [S1832QuotComp]
    apply Quot.sound
    exact ⟨S1728LeftUnitorIso (S1641CoverMapId S1762TerminalCover)⟩
  · show S1832Q S1866DoubledToTerminal ≫ S1832Q S1866TerminalToDoubled =
      𝟙 S1850DoubledCover
    rw [S1832QuotComp]
    apply Quot.sound
    exact ⟨S1728LeftUnitorIso (S1641CoverMapId S1762TerminalCover)⟩

/-- **Coherence is not invariant under isomorphism of recorded covers.**  The
terminal cover is coherent and the doubled cover is not, although they are isomorphic
in `S1728Cover`.  Since the categorical universal property of a fibre product
determines its apex only up to isomorphism, the universal property alone cannot force
the chosen apex presentation to be coherent. -/
theorem S1866Coherence_not_iso_invariant :
    (∃ C : CoherentCover, C.cover = S1762TerminalCover) ∧
      (¬ ∃ C : CoherentCover, C.cover = S1850DoubledCover) ∧
      Nonempty (S1762TerminalCover ≅ S1850DoubledCover) := by
  refine ⟨?_, ?_, S1866TerminalDoubled_iso⟩
  · exact (S1866StrongCoverOf_iff_coherent _).mp S1866StrongCoverOf_terminal
  · intro h
    exact S1866StrongCoverOf_doubled_not
      ((S1866StrongCoverOf_iff_coherent _).mpr h)

/-! ## 3. The S1832 fibre-product data do not determine the apex presentation -/

/-- A two-pullback datum for the identity cospan of the terminal cover whose apex is
the terminal cover itself.  Constructed explicitly (not extracted from a `Nonempty`),
so that its apex is known on the nose. -/
noncomputable def S1866TerminalApexTwoPullback :
    S1832TwoPullback S1866IdentityCoverMap S1866IdentityCoverMap where
  apex := S1762TerminalCover
  toA := S1641CoverMapId S1762TerminalCover
  toB := S1641CoverMapId S1762TerminalCover
  commutes := Iso.refl _
  lift := fun W c => c.toA
  liftToA := fun W c => S1728RightUnitorIso c.toA
  liftToB := fun W c => c.commutes.trans (S1728RightUnitorIso c.toB)
  uniq := fun W c h h1 _ => by
    obtain ⟨e⟩ := h1
    exact ⟨(S1728RightUnitorIso h).symm.trans e⟩

/-- A two-pullback datum for the *same* identity cospan whose apex is the doubled
cover.  It differs from `S1866TerminalApexTwoPullback` only in the recorded
finite-etale data of the apex; every universal-property field is the same because
cover maps see only the source and structure map. -/
noncomputable def S1866DoubledApexTwoPullback :
    S1832TwoPullback S1866IdentityCoverMap S1866IdentityCoverMap where
  apex := S1850DoubledCover
  toA :=
    { map := Pseudofunctor.StrongTrans.id S1850DoubledCover.source.fiber
      commutes := (S1641CoverMapId S1762TerminalCover).commutes }
  toB :=
    { map := Pseudofunctor.StrongTrans.id S1850DoubledCover.source.fiber
      commutes := (S1641CoverMapId S1762TerminalCover).commutes }
  commutes := Iso.refl _
  lift := fun W c =>
    { map := c.toA.map, commutes := c.toA.commutes }
  liftToA := fun W c => S1728RightUnitorIso c.toA
  liftToB := fun W c => c.commutes.trans (S1728RightUnitorIso c.toB)
  uniq := fun W c h h1 _ => by
    obtain ⟨e⟩ := h1
    exact ⟨(S1728RightUnitorIso h).symm.trans e⟩

/-- **The same cospan has two fibre-product data with non-equivalent apex
presentations**: one apex is the coherent terminal cover, the other is the
non-coherent doubled cover.  Hence the S1832 universal property does not determine
whether the apex presentation is coherent. -/
theorem S1866TwoPullbackApexNotDetermined :
    (∃ P : S1832TwoPullback S1866IdentityCoverMap S1866IdentityCoverMap,
        P.apex = S1762TerminalCover) ∧
      (∃ Q : S1832TwoPullback S1866IdentityCoverMap S1866IdentityCoverMap,
        Q.apex = S1850DoubledCover) ∧
      S1866StrongCoverOf S1762TerminalCover ∧
      ¬ S1866StrongCoverOf S1850DoubledCover :=
  ⟨⟨S1866TerminalApexTwoPullback, rfl⟩,
    ⟨S1866DoubledApexTwoPullback, rfl⟩,
    S1866StrongCoverOf_terminal,
    S1866StrongCoverOf_doubled_not⟩

/-- Consequently the natural sufficient condition "every S1832 two-pullback apex is
strong" is **false**: it is refuted by the doubled-apex datum of the identity
cospan.  The exact missing input must be a condition on the *chosen* apex
presentation. -/
theorem S1866TwoPullbackApexAllStrong_false :
    ¬ (∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
        (P : S1832TwoPullback f g), S1866StrongCoverOf P.apex) := by
  intro h
  exact S1866StrongCoverOf_doubled_not
    (h _ _ _ _ _ S1866DoubledApexTwoPullback)

/-! ## 4. The exact first missing for pullbacks -/

/-- **The exact first missing for pullbacks on the coherent covers.**  For every
cospan of coherent covers, the *recorded* weak base-change presentations of the
chosen S1728 pullback apex are strong, i.e. every one of their squares satisfies
`S1852ConeEssSurj`.  This is a plain `Prop` with no inhabitant in this file; it is
proved below to be equivalent to `S1854PullbackApexCoherent h`. -/
def S1866PullbackApexFirstMissing (h : HasPullbacks S1728Cover) : Prop := by
  letI := h
  exact ∀ (A B C : CoherentCover) (f : A.cover ⟶ C.cover) (g : B.cover ⟶ C.cover)
    (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      S1726Orbicurve.stack.fiber),
    S1852ConeEssSurj ((Limits.pullback f g).finiteEtale.baseChange T q)

/-- **The exact first missing is exactly S1854's apex coherence.**  The equivalence
is not a change of assumption: it identifies the missing content as the strongness
of the recorded presentations of the chosen pullback apex. -/
theorem S1866PullbackApexFirstMissing_iff (h : HasPullbacks S1728Cover) :
    S1866PullbackApexFirstMissing h ↔ S1854PullbackApexCoherent h := by
  constructor
  · intro hP
    letI := h
    intro A B C f g
    obtain ⟨P, hPC⟩ := (S1866StrongCoverOf_iff_coherent (Limits.pullback f g)).mp
      ((S1866StrongCoverOf_iff_baseChange (Limits.pullback f g)).mpr (hP A B C f g))
    exact ⟨⟨P, hPC⟩⟩
  · intro hP
    letI := h
    intro A B C f g T q
    obtain ⟨⟨P, hPC⟩⟩ := hP A B C f g
    exact (S1866StrongCoverOf_iff_baseChange (Limits.pullback f g)).mp
      ((S1866StrongCoverOf_iff_coherent (Limits.pullback f g)).mpr ⟨P, hPC⟩) T q

/-- The first missing depends only on the `Prop`-valued `HasPullbacks` structure;
all choices of that structure give the same proposition. -/
theorem S1866PullbackApexFirstMissing_irrelevant
    (h1 h2 : HasPullbacks S1728Cover) :
    S1866PullbackApexFirstMissing h1 = S1866PullbackApexFirstMissing h2 :=
  congrArg S1866PullbackApexFirstMissing (Subsingleton.elim h1 h2)

/-- **The coherent category has pullbacks** from the presentation-level first
missing.  This is the S1856 transport, with the apex condition in its exact
presentation-level form. -/
theorem S1866HasPullbacks (h : HasPullbacks S1728Cover)
    (hA : S1866PullbackApexFirstMissing h) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 :=
  S1856HasPullbacks h ((S1866PullbackApexFirstMissing_iff h).mp hA)

/-- **The coherent Category.{0,1} has pullbacks** from the presentation-level first
missing, at the target hom universe used by S1857/S1875. -/
theorem S1866HasPullbacks01 (h : HasPullbacks S1728Cover)
    (hA : S1866PullbackApexFirstMissing h) :
    @HasPullbacks CoherentCover S1854CoherentCategory01 :=
  S1857HasPullbacks01 h ((S1866PullbackApexFirstMissing_iff h).mp hA)

/-- The presentation-level first missing feeds S1856's named S1832-based first
missing. -/
theorem S1866PullbackFirstMissing_of_S1832 (h : S1832FirstMissingPullback)
    (hA : S1866PullbackApexFirstMissing (S1832HasPullbacks_of_squares h)) :
    S1856PullbackFirstMissing :=
  ⟨h, (S1866PullbackApexFirstMissing_iff _).mp hA⟩

/-- **S1856's pullback first missing, restated at the presentation level.** -/
theorem S1866PullbackFirstMissing_iff :
    S1856PullbackFirstMissing ↔
      ∃ h : S1832FirstMissingPullback,
        S1866PullbackApexFirstMissing (S1832HasPullbacks_of_squares h) :=
  exists_congr (fun h =>
    (S1866PullbackApexFirstMissing_iff (S1832HasPullbacks_of_squares h)).symm)

/-- **The pullback first missing on S1833's affine-equivalence structure.**  This is
the presentation-level condition for the pullback structure transported from an
affine equivalence `e : S1728Cover ≌ (FiniteEtale R')^op`. -/
theorem S1866HasPullbacks_of_affineEquiv (e : S1833AffineEquiv)
    (hA : S1866PullbackApexFirstMissing (S1833HasPullbacks_of_affineEquiv e)) :
    @HasPullbacks CoherentCover S1854CoherentCategory11 :=
  S1866HasPullbacks _ hA

/-! ## 5. The exact first missing for finite coproducts -/

/-- **The exact first missing for finite coproducts on the coherent covers.**  The
recorded weak base-change presentations of the chosen initial object and of every
chosen binary coproduct of coherent covers are strong.  This is a plain `Prop` with
no inhabitant in this file; it is proved below to be equivalent to
`S1854CoproductApexCoherent h0 h2`. -/
def S1866CoproductApexFirstMissing
    (h0 : HasInitial S1728Cover) (h2 : HasBinaryCoproducts S1728Cover) : Prop := by
  letI := h0
  letI := h2
  exact (∀ (T : SchemeOverField S1726K)
      (q : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T)
        S1726Orbicurve.stack.fiber),
      S1852ConeEssSurj ((⊥_ S1728Cover).finiteEtale.baseChange T q)) ∧
    (∀ (A B : CoherentCover) (T : SchemeOverField S1726K)
      (q : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T)
        S1726Orbicurve.stack.fiber),
      S1852ConeEssSurj ((A.cover ⨿ B.cover).finiteEtale.baseChange T q))

/-- **The exact first missing is exactly S1854's coproduct apex coherence.** -/
theorem S1866CoproductApexFirstMissing_iff
    (h0 : HasInitial S1728Cover) (h2 : HasBinaryCoproducts S1728Cover) :
    S1866CoproductApexFirstMissing h0 h2 ↔ S1854CoproductApexCoherent h0 h2 := by
  constructor
  · rintro ⟨hInit, hCop⟩
    letI := h0
    letI := h2
    refine ⟨?_, ?_⟩
    · obtain ⟨P, hPC⟩ :=
        (S1866StrongCoverOf_iff_coherent (⊥_ S1728Cover)).mp
          ((S1866StrongCoverOf_iff_baseChange (⊥_ S1728Cover)).mpr hInit)
      exact ⟨⟨P, hPC⟩⟩
    · intro A B
      obtain ⟨P, hPC⟩ :=
        (S1866StrongCoverOf_iff_coherent (A.cover ⨿ B.cover)).mp
          ((S1866StrongCoverOf_iff_baseChange (A.cover ⨿ B.cover)).mpr (hCop A B))
      exact ⟨⟨P, hPC⟩⟩
  · rintro ⟨hInit, hCop⟩
    letI := h0
    letI := h2
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨P, hPC⟩⟩ := hInit
      exact (S1866StrongCoverOf_iff_baseChange (⊥_ S1728Cover)).mp
        ((S1866StrongCoverOf_iff_coherent (⊥_ S1728Cover)).mpr ⟨P, hPC⟩)
    · intro A B
      obtain ⟨⟨P, hPC⟩⟩ := hCop A B
      exact (S1866StrongCoverOf_iff_baseChange (A.cover ⨿ B.cover)).mp
        ((S1866StrongCoverOf_iff_coherent (A.cover ⨿ B.cover)).mpr ⟨P, hPC⟩)

/-- The coproduct first missing depends only on the `Prop`-valued structures. -/
theorem S1866CoproductApexFirstMissing_irrelevant
    (h0 h0' : HasInitial S1728Cover) (h2 h2' : HasBinaryCoproducts S1728Cover) :
    S1866CoproductApexFirstMissing h0 h2 =
      S1866CoproductApexFirstMissing h0' h2' := by
  rw [Subsingleton.elim h0 h0', Subsingleton.elim h2 h2']

/-- **The coherent category has finite coproducts** from the presentation-level
first missing. -/
theorem S1866HasFiniteCoproducts (h0 : HasInitial S1728Cover)
    (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1866CoproductApexFirstMissing h0 h2) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 :=
  S1856HasFiniteCoproducts h0 h2 ((S1866CoproductApexFirstMissing_iff h0 h2).mp hA)

/-- **The coherent Category.{0,1} has the initial object and binary coproducts**, and
hence finite coproducts, from the presentation-level first missing. -/
theorem S1866HasInitial01 (h0 : HasInitial S1728Cover)
    (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1866CoproductApexFirstMissing h0 h2) :
    @HasInitial CoherentCover S1854CoherentCategory01 :=
  S1857HasInitial01 h0 h2 ((S1866CoproductApexFirstMissing_iff h0 h2).mp hA)

theorem S1866HasBinaryCoproducts01 (h0 : HasInitial S1728Cover)
    (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1866CoproductApexFirstMissing h0 h2) :
    @HasBinaryCoproducts CoherentCover S1854CoherentCategory01 :=
  S1857HasBinaryCoproducts01 h0 h2 ((S1866CoproductApexFirstMissing_iff h0 h2).mp hA)

theorem S1866HasFiniteCoproducts01 (h0 : HasInitial S1728Cover)
    (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1866CoproductApexFirstMissing h0 h2) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory01 :=
  S1857HasFiniteCoproducts01 h0 h2 ((S1866CoproductApexFirstMissing_iff h0 h2).mp hA)

/-- The presentation-level first missing feeds S1856's named S1833-based first
missing. -/
theorem S1866CoproductFirstMissing_of_S1833 (h : S1833FirstMissing)
    (h0 : HasInitial S1728Cover) (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1866CoproductApexFirstMissing h0 h2) :
    S1856CoproductFirstMissing :=
  ⟨h, h0, h2, (S1866CoproductApexFirstMissing_iff h0 h2).mp hA⟩

/-- **S1856's coproduct first missing, restated at the presentation level.** -/
theorem S1866CoproductFirstMissing_iff :
    S1856CoproductFirstMissing ↔
      S1833FirstMissing ∧
        ∃ h0 : HasInitial S1728Cover,
        ∃ h2 : HasBinaryCoproducts S1728Cover,
          S1866CoproductApexFirstMissing h0 h2 := by
  refine and_congr Iff.rfl ?_
  exact exists_congr (fun h0 => exists_congr (fun h2 =>
    (S1866CoproductApexFirstMissing_iff h0 h2).symm))

/-- **The exact first missing in S1833's own objects**: the initial cover
`S1833InitialObj e` and the chosen binary coproducts `S1833CoproductObj e A B` of the
transported affine-equivalence structure carry strong recorded presentations. -/
def S1866CoproductApexFirstMissingAffine (e : S1833AffineEquiv) : Prop :=
  (∀ (T : SchemeOverField S1726K)
      (q : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T)
        S1726Orbicurve.stack.fiber),
      S1852ConeEssSurj ((S1833InitialObj e).finiteEtale.baseChange T q)) ∧
    (∀ (A B : CoherentCover) (T : SchemeOverField S1726K)
      (q : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T)
        S1726Orbicurve.stack.fiber),
      S1852ConeEssSurj
        ((S1833CoproductObj e A.cover B.cover).finiteEtale.baseChange T q))

/-- **The S1833 form of the coproduct first missing is exactly S1854's condition**
for the initial object and binary coproducts transported from an affine equivalence. -/
theorem S1866CoproductApexFirstMissingAffine_iff (e : S1833AffineEquiv) :
    S1866CoproductApexFirstMissingAffine e ↔
      S1854CoproductApexCoherent
        (S1833HasInitial_of_affineEquiv e)
        (S1833HasBinaryCoproducts_of_affineEquiv e) := by
  constructor
  · rintro ⟨hInit, hCop⟩
    letI := S1833HasInitial_of_affineEquiv e
    letI := S1833HasBinaryCoproducts_of_affineEquiv e
    refine ⟨?_, ?_⟩
    · obtain ⟨P, hPC⟩ := (S1866StrongCoverOf_iff_coherent (⊥_ S1728Cover)).mp
        ((S1866StrongCoverOf_iff_baseChange (⊥_ S1728Cover)).mpr hInit)
      exact ⟨⟨P, hPC⟩⟩
    · intro A B
      obtain ⟨P, hPC⟩ := (S1866StrongCoverOf_iff_coherent (A.cover ⨿ B.cover)).mp
        ((S1866StrongCoverOf_iff_baseChange (A.cover ⨿ B.cover)).mpr (hCop A B))
      exact ⟨⟨P, hPC⟩⟩
  · rintro ⟨hInit, hCop⟩
    letI := S1833HasInitial_of_affineEquiv e
    letI := S1833HasBinaryCoproducts_of_affineEquiv e
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨P, hPC⟩⟩ := hInit
      exact (S1866StrongCoverOf_iff_baseChange (⊥_ S1728Cover)).mp
        ((S1866StrongCoverOf_iff_coherent (⊥_ S1728Cover)).mpr ⟨P, hPC⟩)
    · intro A B
      obtain ⟨⟨P, hPC⟩⟩ := hCop A B
      exact (S1866StrongCoverOf_iff_baseChange (A.cover ⨿ B.cover)).mp
        ((S1866StrongCoverOf_iff_coherent (A.cover ⨿ B.cover)).mpr ⟨P, hPC⟩)

/-- The affine form of the coproduct first missing feeds the coherent category's
finite coproducts. -/
theorem S1866HasFiniteCoproducts_of_affineEquiv (e : S1833AffineEquiv)
    (hA : S1866CoproductApexFirstMissingAffine e) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 :=
  S1856HasFiniteCoproducts _ _
    ((S1866CoproductApexFirstMissingAffine_iff e).mp hA)

/-! ## 6. Checks and axiom audit -/

#check S1866StrongCoverOf
#check S1866StrongCoverOf_iff_baseChange
#check S1866StrongCoverOf_iff_coherent
#check S1866StrongCoverOf_terminal
#check S1866StrongCoverOf_doubled_not
#check S1866SameSourceMap_differentStrength
#check S1866IdentityCoverMap
#check S1866TerminalToDoubled
#check S1866DoubledToTerminal
#check S1866TerminalDoubled_iso
#check S1866Coherence_not_iso_invariant
#check S1866TerminalApexTwoPullback
#check S1866DoubledApexTwoPullback
#check S1866TwoPullbackApexNotDetermined
#check S1866TwoPullbackApexAllStrong_false
#check S1866PullbackApexFirstMissing
#check S1866PullbackApexFirstMissing_iff
#check S1866PullbackApexFirstMissing_irrelevant
#check S1866HasPullbacks
#check S1866HasPullbacks01
#check S1866PullbackFirstMissing_of_S1832
#check S1866PullbackFirstMissing_iff
#check S1866HasPullbacks_of_affineEquiv
#check S1866CoproductApexFirstMissing
#check S1866CoproductApexFirstMissing_iff
#check S1866CoproductApexFirstMissing_irrelevant
#check S1866HasFiniteCoproducts
#check S1866HasInitial01
#check S1866HasBinaryCoproducts01
#check S1866HasFiniteCoproducts01
#check S1866CoproductFirstMissing_of_S1833
#check S1866CoproductFirstMissing_iff
#check S1866CoproductApexFirstMissingAffine
#check S1866CoproductApexFirstMissingAffine_iff
#check S1866HasFiniteCoproducts_of_affineEquiv

#print axioms S1866StrongCoverOf_iff_baseChange
#print axioms S1866StrongCoverOf_iff_coherent
#print axioms S1866StrongCoverOf_terminal
#print axioms S1866StrongCoverOf_doubled_not
#print axioms S1866SameSourceMap_differentStrength
#print axioms S1866TerminalDoubled_iso
#print axioms S1866Coherence_not_iso_invariant
#print axioms S1866TerminalApexTwoPullback
#print axioms S1866DoubledApexTwoPullback
#print axioms S1866TwoPullbackApexNotDetermined
#print axioms S1866TwoPullbackApexAllStrong_false
#print axioms S1866PullbackApexFirstMissing_iff
#print axioms S1866PullbackApexFirstMissing_irrelevant
#print axioms S1866HasPullbacks
#print axioms S1866HasPullbacks01
#print axioms S1866PullbackFirstMissing_of_S1832
#print axioms S1866PullbackFirstMissing_iff
#print axioms S1866HasPullbacks_of_affineEquiv
#print axioms S1866CoproductApexFirstMissing_iff
#print axioms S1866CoproductApexFirstMissing_irrelevant
#print axioms S1866HasFiniteCoproducts
#print axioms S1866HasInitial01
#print axioms S1866HasBinaryCoproducts01
#print axioms S1866HasFiniteCoproducts01
#print axioms S1866CoproductFirstMissing_of_S1833
#print axioms S1866CoproductFirstMissing_iff
#print axioms S1866CoproductApexFirstMissingAffine_iff
#print axioms S1866HasFiniteCoproducts_of_affineEquiv

end LeanFormal.IUT.XiFPaper.S1866ApexCoherenceActual