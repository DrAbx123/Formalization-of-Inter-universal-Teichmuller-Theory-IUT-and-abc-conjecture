import tmp.sheaf.xif.paper.KappaOrbitPairActualAdapted
import tmp.sheaf.xif.paper.PaperThetaLinkNontrivial

/-! # CONDITIONAL STATUS (xi-f)

Conditional: strip links are actual, but LinkedCommonGroup / LowerKappaDonor / linked kappa representative are missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Lower kappa donor attempt for S00/S01 and S01/S11

Task-603 write-only attempt.

Actual strips:
  S00 = I.primeStripAt 0 0
  S01 = I.primeStripAt 0 1
  S11 = I.primeStripAt 1 1

Actual strip links constructed here from the source Hodge-theater links:
  linkS00S01 : FPrimeStripEquiv S00 S01 := (I.linkAt 0 0 0 1).primeStripEquiv
  linkS01S11 : FPrimeStripEquiv S01 S11 := (I.linkAt 0 1 1 1).primeStripEquiv

The exact LowerKappaDonor type from KappaOrbitPairActualAdapted is
  forall v, TimesMuKummer.Isomorphism
    (pairUnitsActionUpper upper lower v)
    (pairUnitsActionLower upper lower v).

No production theorem constructs this donor from the actual strip links. The
obstruction is structural: the production pair group is the product of the
upper and lower local groups at each v, and pairUnitsActionUpper depends only
on the upper component while pairUnitsActionLower depends only on the lower
component. A strip link only relates the two components on the graph of its
isoPi; it does not identify the independent product components. Thus the
required Isomorphism is not a consequence of the link alone; the missing
object is a link-compatible common group (a graph/diagonal subgroup carrying
both actions) or an explicit lower kappa representative on such a group.

This file records:
* the actual link equivalences;
* a conditional donor-to-pair construction reusing KappaOrbitPairActualAdapted;
* the exact missing graph-group / donor interface;
* no assertion that the donor exists.

No identity pair, toy action, True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LowerKappaDonorActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial
open LeanFormal.IUT.XiFPaper.KappaOrbitPairActualAdapted

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual source link S00 -> S01. -/
def linkS00S01 : FPrimeStripEquiv (S00 (I := I)) (S01 (I := I)) :=
  (I.linkAt 0 0 0 1).primeStripEquiv

/-- The actual source link S01 -> S11. -/
def linkS01S11 : FPrimeStripEquiv (S01 (I := I)) (S11 (I := I)) :=
  (I.linkAt 0 1 1 1).primeStripEquiv

/-- The exact donor for the first pair. -/
abbrev LowerKappaDonorS00S01 : Type _ :=
  LowerKappaDonor (V := V) (S00 (I := I)) (S01 (I := I))

/-- The exact donor for the second pair. -/
abbrev LowerKappaDonorS01S11 : Type _ :=
  LowerKappaDonor (V := V) (S01 (I := I)) (S11 (I := I))

/-- The actual upper action is recovered from the production pair action. -/
theorem pairUnitsActionUpper_apply
    (upper lower : FPrimeStrip V) (v : V)
    (f : pairGroup (V := V) upper lower) (u : (upper.Mon v)ˣ) :
    FPrimeStrip.pairUnitsActionUpper upper lower v f u =
      upper.unitsAction v (f v).1 u := rfl

/-- The actual lower action is recovered from the production pair action. -/
theorem pairUnitsActionLower_apply
    (upper lower : FPrimeStrip V) (v : V)
    (f : pairGroup (V := V) upper lower) (u : (lower.Mon v)ˣ) :
    FPrimeStrip.pairUnitsActionLower upper lower v f u =
      lower.unitsAction v (f v).2 u := rfl

/-- A lower kappa donor yields the actual KappaOrbitUnitsActionPairDatum for
the first pair. -/
noncomputable def pairS00S01OfDonor
    [TopologicalSpace (pairGroup (V := V) (S00 (I := I)) (S01 (I := I)))]
    (h : LowerKappaDonorS00S01 (I := I)) :
    KappaOrbitUnitsActionPairDatum
      (pairGroup (V := V) (S00 (I := I)) (S01 (I := I)))
      (S00 (I := I)) (S01 (I := I)) :=
  pairOfLowerKappa (S00 (I := I)) (S01 (I := I)) h

/-- A lower kappa donor yields the actual KappaOrbitUnitsActionPairDatum for
the second pair. -/
noncomputable def pairS01S11OfDonor
    [TopologicalSpace (pairGroup (V := V) (S01 (I := I)) (S11 (I := I)))]
    (h : LowerKappaDonorS01S11 (I := I)) :
    KappaOrbitUnitsActionPairDatum
      (pairGroup (V := V) (S01 (I := I)) (S11 (I := I)))
      (S01 (I := I)) (S11 (I := I)) :=
  pairOfLowerKappa (S01 (I := I)) (S11 (I := I)) h

/-- Exact missing first donor. -/
abbrev MissingLowerKappaS00S01 : Prop :=
  Nonempty (LowerKappaDonorS00S01 (I := I))

/-- Exact missing second donor. -/
abbrev MissingLowerKappaS01S11 : Prop :=
  Nonempty (LowerKappaDonorS01S11 (I := I))

/-- The link-compatible common-group interface: a group G with factorizations
whose lower factor is the link image of the upper factor. -/
structure LinkedCommonGroup
    (upper lower : FPrimeStrip V) (link : FPrimeStripEquiv upper lower) where
  G : Type uG
  [groupG : Group G]
  factorUpper : ∀ v : V, G →* upper.toDPrimeStrip.Pi v
  factorLower : ∀ v : V, G →* lower.toDPrimeStrip.Pi v
  factorLower_eq : ∀ v, factorLower v = (link.isoPi v).comp (factorUpper v)

attribute [instance] LinkedCommonGroup.groupG

/-- The exact missing object is a linked common group carrying both actual
strip actions, together with a lower kappa representative for the resulting
linked actions. -/
structure MissingLinkedKappaData
    (upper lower : FPrimeStrip V) (link : FPrimeStripEquiv upper lower) where
  common : LinkedCommonGroup upper lower link
  /-- a lower Kummer representative on the linked common group. -/
  kappaLower : ∀ v : V, TimesMuKummer.Isomorphism
    ((upper.unitsAction v).comp (common.factorUpper v))
    ((lower.unitsAction v).comp (common.factorLower v))

/-- The exact missing linked data package for the two actual strip links. -/
structure MissingLinkedKappaPackage : Prop where
  first : Nonempty (MissingLinkedKappaData
    (S00 (I := I)) (S01 (I := I)) (linkS00S01 (I := I)))
  second : Nonempty (MissingLinkedKappaData
    (S01 (I := I)) (S11 (I := I)) (linkS01S11 (I := I)))

/-- Exact status: the actual links are available, but neither the product
pair donor nor the linked common-group lower kappa is constructed. -/
theorem lowerKappaDonorActual_status :
    (FPrimeStripEquiv (S00 (I := I)) (S01 (I := I))) ∧
      (FPrimeStripEquiv (S01 (I := I)) (S11 (I := I))) ∧
      (Nonempty (LowerKappaDonorS00S01 (I := I)) ->
        Nonempty (KappaOrbitUnitsActionPairDatum
          (pairGroup (V := V) (S00 (I := I)) (S01 (I := I)))
          (S00 (I := I)) (S01 (I := I)))) ∧
      (Nonempty (LowerKappaDonorS01S11 (I := I)) ->
        Nonempty (KappaOrbitUnitsActionPairDatum
          (pairGroup (V := V) (S01 (I := I)) (S11 (I := I)))
          (S01 (I := I)) (S11 (I := I)))) := by
  refine ⟨linkS00S01 (I := I), linkS01S11 (I := I), ?_, ?_⟩
  · rintro ⟨h⟩
    letI : TopologicalSpace (pairGroup (V := V) (S00 (I := I)) (S01 (I := I))) := ⊥
    exact ⟨pairS00S01OfDonor (I := I) h⟩
  · rintro ⟨h⟩
    letI : TopologicalSpace (pairGroup (V := V) (S01 (I := I)) (S11 (I := I))) := ⊥
    exact ⟨pairS01S11OfDonor (I := I) h⟩

end LeanFormal.IUT.XiFPaper.LowerKappaDonorActualAdapted

end
