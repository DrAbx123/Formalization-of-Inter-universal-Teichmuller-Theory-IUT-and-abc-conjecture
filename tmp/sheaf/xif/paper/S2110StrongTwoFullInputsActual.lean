import tmp.sheaf.xif.paper.S2097BaseChangeButterflyActual
import tmp.sheaf.xif.paper.S2100GPresentationConeEssSurjActual
import tmp.sheaf.xif.paper.S2103StrongAssemblyActual
import tmp.sheaf.xif.paper.S2108PastedTransportActual

/-!
# S2110: the strong two-full-inputs reduction of the butterfly base change

## The target

S2097 reduced `S2086BaseChangePullback` to two full inputs plus the pasted-square
transport, and S2108 constructed that transport.  The remaining second input was
still `S2094GPresentationConeEssSurj`, i.e.

  forall (A B C) (f : A -> C) (g : B -> C) (T) (ptA)
    (Pg : EtaleStackBaseChangePresentation g.map T (ptA ; f.map)),
    S1852ConeEssSurj Pg.

S2100 proved that statement **false** (the doubled cover presentation of the
identity cover map violates `S1852ConeEssSurj`), and isolated the corrected input
`S2100StrongGPresentationInput`: instead of quantifying over an arbitrary weak
presentation, choose the strong presentation of `g.map` at the used point.  S2103
packaged the geometric form of the correction as
`S2103StrongCospanGMapFiniteEtale` (a `StrongEtaleStackFiniteEtaleMorphism` on
every cover map) and used it for the D6(c) assembly.

This file adapts the S2108/S2097 chain to the strong input.  Nothing in S2097 or
S2108 is changed, and the false `S2094GPresentationConeEssSurj` is nowhere used.

## What is proved here

* `S2110StrongBaseChangePullback hG`: the strong-indexed analogue of
  `S2086BaseChangePullback`.  For every cospan, test point and the strong
  presentation `hG` selects, the explicit base-change square `S2086ToASquare` is
  a two-pullback.  No statement is made about an arbitrary weak presentation.

* `S2110PastedSquareFull` and `S2110StrongPastedTransport`: the strong form of
  S2108's `S2108PastedSquareFull` / `S2108PastedTransport`.  The weak presentation
  `Pg` plus the hypothesis `S1852ConeEssSurj Pg` are replaced by a single
  `StrongEtaleStackBaseChangePresentation Pg`; the transport itself is exactly
  S2108's, applied to `Pg.toWeak` and the strong field `Pg.coneEssSurj`.

* `S2110StrongTwoFullData` and `S2110StrongTwoFullData.ofInputs`: the honest
  replacement of `S2097TwoFullInputs` / `S2108TwoFullInputs`.  The bundle keeps
  the big-square input and the pasted transport, but its second field is the
  strong presentation input, not the false `S2094GPresentationConeEssSurj`.

* `S2110BaseChangePullback_of_twoFullInputs`: the S2097 right-cancellation step
  applied to the strong bundle; it produces the strong-indexed pullback statement
  from `S2097RightCancelStatement` and the bundle.

* `S2110StrongGPresentationTwoFullInputs`: the direct form, taking only
  `S2097RightCancelStatement`, `S2094BigSquareEssSurj` and
  `S2100StrongGPresentationInput`.

* `S2110StrongCospanToWeak` / `S2110StrongCospanToInput`: a strong finite-etale
  structure forgets to the weak structure of S2086 and yields the strong
  presentation input.  The two forgetful maps are definitional, so the following
  two results are literally in the S2086/S2103 types.

* `S2110StrongTwoFullInputs`: **the main result**.  For every cover map carrying
  a strong finite-etale structure (`hg : S2103StrongCospanGMapFiniteEtale`), the
  S2086 base-change pullback holds for the weak structure `hg.toWeak`:

    `S2086BaseChangePullback (S2110StrongCospanToWeak hg)`.

  Only `S2097RightCancelStatement`, `S2094BigSquareEssSurj` and the strong
  finite-etale structure are assumed.  This is the strong replacement of
  `S2108BaseChangePullback_of_rightCancel`, with the false `hG` removed.

* `S2110StrongCospanPullback`: the same result in the S2103 normal form
  `S2103StrongBaseChangePullback hg`.

* `S2110ToAOfStrongInputs` and `S2110D6FiniteEtale`: the S2103 consumers, i.e.
  `S2044ToAFiniteEtaleField` and D6(c) `S2043FirstMissingFiniteEtale` for every
  cospan, obtained through the strong assembly.

## Honest boundary

* No `sorry`, no new axiom, no fabricated presentation or two-pullback witness.
  Every field of `S2110StrongTwoFullData` is constructed; the pasted transport is
  the proved S2108 transport.

* `S2097RightCancelStatement` and `S2094BigSquareEssSurj` remain the two genuine
  missing 2-categorical inputs.  They are taken as hypotheses, exactly as in
  S2097/S2108; this file does not claim them.

* `S2100StrongGPresentationInput` is a Type-valued input, not a proposition
  derived from the weak witness.  No inhabitant is asserted here.

* The S2086 statement is proved for the weak finite-etale structure obtained by
  forgetting a *given* strong finite-etale structure (`hg.toWeak`).  It is not
  claimed for an arbitrary weak `hg`: the strong data concerns a different
  presentation, and S2100's counterexample shows that the universal weak claim
  cannot be recovered.  The strong-indexed form
  `S2110StrongBaseChangePullback hG` is stated separately for the S2100 interface.

* The axiom footprint is `propext`, `Classical.choice`, `Quot.sound`; see the
  audit at the end.  No `sorryAx`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2110StrongTwoFullInputsActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2100GPresentationConeEssSurjActual
open LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual

universe u

/-! ## 1. The strong-indexed target

`S2086BaseChangePullback` is indexed by a *weak* finite-etale structure: for each
cospan it tests the weak presentation selected by that structure.  The strong
statement quantifies over the strong presentations selected by
`S2100StrongGPresentationInput` instead.  It is the exact statement transported
by S2108 in this file. -/

/-- **The strong-indexed analogue of `S2086BaseChangePullback`.**  For every
cospan, test scheme and test point, the explicit base-change square built from the
strong presentation `hG` selects is a two-pullback. -/
def S2110StrongBaseChangePullback (hG : S2100StrongGPresentationInput) : Type _ :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    (S2086ToASquare f g T ptA (hG A B C f g T ptA).toWeak).TwoPullbackWitness

/-! ## 2. The pasted transport for a strong presentation

S2108's transport needs a weak presentation together with
`S1852ConeEssSurj`.  A strong presentation is precisely such a pair, so the
transport applies verbatim to its weak image; this is the only place where the
strong input enters the S2108 chain. -/

/-- **S2108's pasted transport for a strong presentation.**  The weak
presentation `Pg.toWeak` and its full cone essential-surjectivity
`Pg.coneEssSurj` give the full pasted-square datum. -/
noncomputable def S2110PastedSquareFull {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    S2097PastedSquareFull f g T ptA Pg.toWeak :=
  S2108PastedSquareFull f g T ptA Pg.toWeak Pg.coneEssSurj

/-- **The strong form of `S2108PastedTransport`**: the same function type, with
the weak presentation `Pg` and the hypothesis `S1852ConeEssSurj Pg` replaced by a
single strong presentation.  This preserves the S2108 transport structure while
removing the false universal hypothesis. -/
noncomputable def S2110StrongPastedTransport :
    forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
      (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
      S2097PastedSquareFull f g T ptA Pg.toWeak :=
  fun A B C f g T ptA Pg => S2110PastedSquareFull f g T ptA Pg

/-! ## 3. The strong two-full-inputs bundle

This is the honest replacement of `S2097TwoFullInputs` and `S2108TwoFullInputs`.
The big-square input and the pasted transport are kept; the second field is the
strong presentation input rather than `S2094GPresentationConeEssSurj`. -/

/-- **The strong two-full-inputs bundle.**  `bigSquare` is S2094's first input;
`strongPresentation` is S2100's corrected second input; `pastedTransport` is the
transport of `2.  No false universal hypothesis over weak presentations occurs. -/
structure S2110StrongTwoFullData : Type 1 where
  /-- S2094 input 1: `S1827EssSurjOf` for the iso-comma square. -/
  bigSquare : S2094BigSquareEssSurj
  /-- S2100's corrected input 2: the strong presentation of `g.map` at every
  used point. -/
  strongPresentation : S2100StrongGPresentationInput
  /-- The pasted-square transport, from S2108, for the selected strong
  presentations. -/
  pastedTransport : forall (A B C : S1728Cover) (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    S2097PastedSquareFull f g T ptA
      (strongPresentation A B C f g T ptA).toWeak

/-- **The strong replacement of `S2108TwoFullInputs`**: the big-square input and
`S2100StrongGPresentationInput` construct the strong bundle, with the pasted
transport filled by `S2110StrongPastedTransport`.  The false
`S2094GPresentationConeEssSurj` is gone. -/
noncomputable def S2110StrongTwoFullData.ofInputs
    (hBig : S2094BigSquareEssSurj) (hG : S2100StrongGPresentationInput) :
    S2110StrongTwoFullData where
  bigSquare := hBig
  strongPresentation := hG
  pastedTransport := fun A B C f g T ptA =>
    S2110PastedSquareFull f g T ptA (hG A B C f g T ptA)

/-! ## 4. The butterfly pullback from the strong bundle

The S2097 right-cancellation step consumes the pasted-square full datum at the
weak image of the chosen strong presentation.  Everything is now constructed. -/

/-- **The strong analogue of `S2097BaseChangePullback_of_rightCancel` and
`S2108BaseChangePullback_of_rightCancel`**: the right-cancellation lemma applied
to the strong bundle gives the strong-indexed base-change pullback. -/
noncomputable def S2110BaseChangePullback_of_twoFullInputs
    (hRC : S2097RightCancelStatement) (h : S2110StrongTwoFullData) :
    S2110StrongBaseChangePullback h.strongPresentation := by
  intro A B C f g T ptA
  exact S2097BaseChangePullback_of_rightCancel f g T ptA
    (h.strongPresentation A B C f g T ptA).toWeak hRC h.bigSquare
    (h.pastedTransport A B C f g T ptA)

/-- **The direct strong reduction**: `S2097RightCancelStatement`,
`S2094BigSquareEssSurj` and `S2100StrongGPresentationInput` alone give the
strong-indexed base-change pullback. -/
noncomputable def S2110StrongGPresentationTwoFullInputs
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hG : S2100StrongGPresentationInput) :
    S2110StrongBaseChangePullback hG :=
  S2110BaseChangePullback_of_twoFullInputs hRC (S2110StrongTwoFullData.ofInputs hBig hG)

/-! ## 5. From strong finite-etale structures back to S2086/S2103

A `StrongEtaleStackFiniteEtaleMorphism` forgets to the recorded weak
finite-etale structure `EtaleStackFiniteEtaleMorphism` (S1852), with the same
base-change presentations.  Hence a strong finite-etale structure on every cover
map yields both the S2100 strong input and the weak structure expected by
`S2086BaseChangePullback`.  Both forgetful maps are definitional (`rfl`), so the
results below are literally in the S2086/S2103 types. -/

/-- The weak finite-etale structure underlying a strong one (S1852's
`StrongEtaleStackFiniteEtaleMorphism.toWeak`, applied pointwise). -/
def S2110StrongCospanToWeak (hg : S2103StrongCospanGMapFiniteEtale) :
    S2086CospanGMapFiniteEtale :=
  fun A B C f g => (hg A B C f g).toWeak

/-- The strong presentation input selected by a strong finite-etale structure. -/
def S2110StrongCospanToInput (hg : S2103StrongCospanGMapFiniteEtale) :
    S2100StrongGPresentationInput :=
  fun A B C f g T ptA => (hg A B C f g).baseChange T (S2086PointC f ptA)

/-- The weak base-change presentation of `S2110StrongCospanToWeak hg` is exactly
the weak image of the strong presentation selected by `hg`; this is the
definitional identity that makes the S2086/S2103 types match. -/
theorem S2110StrongCospanToWeak_baseChange
    (hg : S2103StrongCospanGMapFiniteEtale)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    (S2110StrongCospanToWeak hg A B C f g).baseChange T (S2086PointC f ptA) =
      ((hg A B C f g).baseChange T (S2086PointC f ptA)).toWeak :=
  rfl

/-- **The main result: the strong two-full-inputs theorem in the S2086 type.**
For every cospan of cover maps carrying a strong finite-etale structure `hg`, the
explicit base-change square of `S2086ToASquare` is a two-pullback for the weak
structure `hg.toWeak`.  The only assumptions are S2097's right-cancellation
lemma, S2094's big-square essential-surjectivity and the strong finite-etale
structure; `S2094GPresentationConeEssSurj` is not used and is false (S2100). -/
noncomputable def S2110StrongTwoFullInputs
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hg : S2103StrongCospanGMapFiniteEtale) :
    S2086BaseChangePullback (S2110StrongCospanToWeak hg) := by
  intro A B C f g T ptA
  exact S2110StrongGPresentationTwoFullInputs hRC hBig
    (S2110StrongCospanToInput hg) A B C f g T ptA

/-- **The S2103 normal form**: the same result is literally
`S2103StrongBaseChangePullback hg`, since S2103's type tests the weak image of
exactly the strong presentations selected by `hg`. -/
noncomputable def S2110StrongCospanPullback
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hg : S2103StrongCospanGMapFiniteEtale) :
    S2103StrongBaseChangePullback hg :=
  S2110StrongTwoFullInputs hRC hBig hg

/-! ## 6. Consumers: the S2103 assembly and D6(c)

These are the actual consumers of `S2110StrongCospanPullback`: S2103's
`S2103ToAOfStrongInputs` and `S2103D6FiniteEtaleOfStrongInputs`, now with their
last conditional input discharged by S2110. -/

/-- `S2044ToAFiniteEtaleField` from the strong inputs. -/
noncomputable def S2110ToAOfStrongInputs
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hg : S2103StrongCospanGMapFiniteEtale) :
    S2044ToAFiniteEtaleField :=
  S2103ToAOfStrongInputs hg (S2110StrongCospanPullback hRC hBig hg)

/-- **D6(c) finite etaleness of the composite structure map** from the strong
inputs, for every cospan of cover maps. -/
noncomputable def S2110D6FiniteEtale
    (hRC : S2097RightCancelStatement)
    (hBig : S2094BigSquareEssSurj)
    (hg : S2103StrongCospanGMapFiniteEtale)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (A := A) (B := B) (C := C) (f := f) (g := g) :=
  S2103D6FiniteEtaleOfStrongInputs hg (S2110StrongCospanPullback hRC hBig hg) f g

/-! ## 7. Checks -/

#check S2110StrongBaseChangePullback
#check S2110StrongGPresentationTwoFullInputs
#check @S2110StrongPastedTransport
#check S2110StrongTwoFullData
#check S2110StrongTwoFullData.ofInputs
#check S2110BaseChangePullback_of_twoFullInputs
#check S2110StrongCospanToWeak
#check S2110StrongCospanToInput
#check S2110StrongCospanToWeak_baseChange
#check S2110StrongTwoFullInputs
#check S2110StrongCospanPullback
#check S2110ToAOfStrongInputs
#check S2110D6FiniteEtale

#print axioms S2110PastedSquareFull
#print axioms S2110StrongPastedTransport
#print axioms S2110StrongTwoFullData.ofInputs
#print axioms S2110BaseChangePullback_of_twoFullInputs
#print axioms S2110StrongGPresentationTwoFullInputs
#print axioms S2110StrongCospanToWeak
#print axioms S2110StrongCospanToWeak_baseChange
#print axioms S2110StrongTwoFullInputs
#print axioms S2110StrongCospanPullback
#print axioms S2110ToAOfStrongInputs
#print axioms S2110D6FiniteEtale

end LeanFormal.IUT.XiFPaper.S2110StrongTwoFullInputsActual

end
