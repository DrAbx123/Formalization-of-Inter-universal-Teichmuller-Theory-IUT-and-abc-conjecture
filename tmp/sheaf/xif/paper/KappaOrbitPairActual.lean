import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitFactorizationProvider
import tmp.sheaf.xif.paper.PaperThetaLinkNontrivial

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Kappa-orbit pair datum from actual strip actions and one missing lower kappa

Task-591 write-only attempt.

Actual strips (PaperThetaLinkNontrivial):
  S00 = I.primeStripAt 0 0
  S01 = I.primeStripAt 0 1
  S11 = I.primeStripAt 1 1

Actual production data used:
* FPrimeStrip.pairFactorizationUpper/Lower and pairUnitsActionUpper/Lower:
  the common product group
    (v : V) -> upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v
  with its actual projection factorizations and actual units actions;
* TimesMuKummer.Isomorphism.refl: the actual upper representative for the
  identity comparison between sourceAction and the upper units action.

Constructed conditionally here:
* KappaOrbitUnitsActionPairDatum for (S00, S01);
* KappaOrbitUnitsActionPairDatum for (S01, S11).

In both constructions:
  sourceUnits v   := (upper.Mon v)^x
  sourceAction v  := pairUnitsActionUpper upper lower v
  factorUpper v   := pairFactorizationUpper upper lower v
  factorLower v   := pairFactorizationLower upper lower v
  kappaUpper v    := Isomorphism.refl (pairUnitsActionUpper ...)
  kappaLower v    := the supplied lower kappa.

Exact missing source field:
  kappaLower v : TimesMuKummer.Isomorphism
      (pairUnitsActionUpper upper lower v)
      (pairUnitsActionLower upper lower v)
for each of the two strip pairs. No production constructor of this lower
Kummer representative from the actual strip links exists: the concrete
KappaOrbitUnitsActionDatum provider supplies one strip at a time and its
canonical completion makes the source and target actions identical, while the
pair datum requires a genuine upper-to-lower representative. The actual strip
links S00 -> S01 and S01 -> S11 supply FPrimeStripEquiv data, but the tree has
no theorem turning those links into the required TimesMuKummer.Isomorphism.

No identity pair, trivial action, True/PUnit, axiom, or sorry is used. The
pair is not asserted to exist; only its exact lower-kappa donor is recorded.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.KappaOrbitPairActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual four-corner strips. -/
abbrev S00 : FPrimeStrip V := upperLeftStrip (I := I)
abbrev S01 : FPrimeStrip V := upperRightStrip (I := I)
abbrev S11 : FPrimeStrip V := lowerRightStrip (I := I)

/-- The canonical common product group for a strip pair. -/
abbrev pairGroup (upper lower : FPrimeStrip V) : Type _ :=
  ((v : V) → upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v)

/-- The exact lower-kappa donor for a strip pair. -/
abbrev LowerKappaDonor (upper lower : FPrimeStrip V) : Type _ :=
  ∀ v : V, TimesMuKummer.Isomorphism
    (FPrimeStrip.pairUnitsActionUpper upper lower v)
    (FPrimeStrip.pairUnitsActionLower upper lower v)

/-- Build a kappa-orbit pair datum from the actual upper actions and a supplied
lower kappa representative. -/
noncomputable def pairOfLowerKappa
    (upper lower : FPrimeStrip V)
    [TopologicalSpace (pairGroup (V := V) upper lower)]
    (kappaLower : LowerKappaDonor (V := V) upper lower) :
    KappaOrbitUnitsActionPairDatum (pairGroup (V := V) upper lower) upper lower where
  sourceUnits := fun v => (upper.Mon v)ˣ
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := fun v => FPrimeStrip.pairUnitsActionUpper upper lower v
  factorUpper := fun v => FPrimeStrip.pairFactorizationUpper upper lower v
  factorLower := fun v => FPrimeStrip.pairFactorizationLower upper lower v
  kappaUpper := fun v =>
    TimesMuKummer.Isomorphism.refl
      (FPrimeStrip.pairUnitsActionUpper upper lower v)
  kappaLower := kappaLower

/-- The upper representative of the constructed pair is the actual identity
comparison. -/
theorem pairOfLowerKappa_kappaUpper
    (upper lower : FPrimeStrip V)
    [TopologicalSpace (pairGroup (V := V) upper lower)]
    (kappaLower : LowerKappaDonor (V := V) upper lower) (v : V) :
    (pairOfLowerKappa upper lower kappaLower).kappaUpper v =
      TimesMuKummer.Isomorphism.refl
        (FPrimeStrip.pairUnitsActionUpper upper lower v) := rfl

/-- The source action of the constructed pair is the actual upper strip
action. -/
theorem pairOfLowerKappa_sourceAction
    (upper lower : FPrimeStrip V)
    [TopologicalSpace (pairGroup (V := V) upper lower)]
    (kappaLower : LowerKappaDonor (V := V) upper lower) (v : V) :
    (pairOfLowerKappa upper lower kappaLower).sourceAction v =
      FPrimeStrip.pairUnitsActionUpper upper lower v := rfl

/-- The lower factor of the constructed pair is the actual lower projection. -/
theorem pairOfLowerKappa_factorLower
    (upper lower : FPrimeStrip V)
    [TopologicalSpace (pairGroup (V := V) upper lower)]
    (kappaLower : LowerKappaDonor (V := V) upper lower) (v : V) :
    (pairOfLowerKappa upper lower kappaLower).factorLower v =
      FPrimeStrip.pairFactorizationLower upper lower v := rfl

/-- The actual S00 -> S01 pair, conditional on the lower kappa donor. -/
noncomputable def pairS00S01
    [TopologicalSpace (pairGroup (V := V) S00 S01)]
    (kappaLower : LowerKappaDonor (V := V) S00 S01) :
    KappaOrbitUnitsActionPairDatum (pairGroup (V := V) S00 S01) S00 S01 :=
  pairOfLowerKappa (S00 (I := I)) (S01 (I := I)) kappaLower

/-- The actual S01 -> S11 pair, conditional on the lower kappa donor. -/
noncomputable def pairS01S11
    [TopologicalSpace (pairGroup (V := V) S01 S11)]
    (kappaLower : LowerKappaDonor (V := V) S01 S11) :
    KappaOrbitUnitsActionPairDatum (pairGroup (V := V) S01 S11) S01 S11 :=
  pairOfLowerKappa (S01 (I := I)) (S11 (I := I)) kappaLower

/-- Exact missing donor for the first pair. -/
abbrev MissingLowerKappaS00S01 : Prop :=
  Nonempty (LowerKappaDonor (V := V) S00 S01)

/-- Exact missing donor for the second pair. -/
abbrev MissingLowerKappaS01S11 : Prop :=
  Nonempty (LowerKappaDonor (V := V) S01 S11)

/-- Exact missing package for both pairs. -/
structure MissingLowerKappas : Prop where
  first : MissingLowerKappaS00S01 (I := I)
  second : MissingLowerKappaS01S11 (I := I)

/-- The exact status: the pair datum is constructed from the actual upper
actions and the lower kappa donor; the donor itself is not constructed. -/
theorem kappaPairActual_status :
    (Nonempty (LowerKappaDonor (V := V) S00 S01) ->
      Nonempty (KappaOrbitUnitsActionPairDatum
        (pairGroup (V := V) S00 S01) S00 S01)) ∧
    (Nonempty (LowerKappaDonor (V := V) S01 S11) ->
      Nonempty (KappaOrbitUnitsActionPairDatum
        (pairGroup (V := V) S01 S11) S01 S11)) := by
  constructor
  · rintro ⟨h⟩
    letI : TopologicalSpace (pairGroup (V := V) S00 S01) := ⊥
    exact ⟨pairS00S01 (I := I) h⟩
  · rintro ⟨h⟩
    letI : TopologicalSpace (pairGroup (V := V) S01 S11) := ⊥
    exact ⟨pairS01S11 (I := I) h⟩

end LeanFormal.IUT.XiFPaper.KappaOrbitPairActual

end
