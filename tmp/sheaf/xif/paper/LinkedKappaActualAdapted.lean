import tmp.sheaf.xif.paper.LowerKappaDonorActualAdapted
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism

/-! # CONDITIONAL STATUS (xi-f)

Partial actual linked group/kappa construction; LowerKappaDonor/linked kappa data remain conditional/missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Linked common group and lower kappa from an actual strip link

Task-609 write-only construction.

Given an actual FPrimeStripEquiv link : FPrimeStripEquiv upper lower, this file
constructs:

* graphGroup upper := (v : V) -> upper.toDPrimeStrip.Pi v;
* the projection evaluation factorization;
* a LinkedCommonGroup with
    factorUpper v := evaluation at v,
    factorLower v := (link.isoPi v).comp (evaluation at v),
    factorLower_eq := rfl;
* a lower TimesMuKummer.Isomorphism between the two induced units actions,
  with equiv := TimesMuQuotient.congr (Units.mapEquiv (link.isoMon v));
* the actual MissingLinkedKappaData package from LowerKappaDonorActualAdapted;
* the two concrete packages for S00 -> S01 and S01 -> S11 using the actual
  source links linkS00S01 and linkS01S11.

The equivariance proof uses FPrimeStripEquiv.unitsAction_compat. The
invariant-image proof uses the unit-fixed representative characterization of
TimesMuKummer.invariantImage and the same compatibility.

No identity/toy group, no True/PUnit, no axiom or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LinkedKappaActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial
open LeanFormal.IUT.XiFPaper.LowerKappaDonorActualAdapted
open LeanFormal.IUT.TimesMuQuotient

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {upper lower : FPrimeStrip V}

/-- The graph group of a strip: the product of its local groups. -/
abbrev graphGroup (upper : FPrimeStrip V) : Type _ :=
  ((v : V) → upper.toDPrimeStrip.Pi v)

/-- Evaluation at a place, the canonical projection factorization. -/
def graphEval (upper : FPrimeStrip V) (v : V) :
    graphGroup (V := V) upper →* upper.toDPrimeStrip.Pi v where
  toFun f := f v
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem graphEval_apply (upper : FPrimeStrip V) (v : V)
    (f : graphGroup (V := V) upper) :
    graphEval upper v f = f v := rfl

/-- The linked common group from an actual strip equivalence. -/
def linkedCommonGroup (link : FPrimeStripEquiv upper lower) :
    LinkedCommonGroup upper lower link where
  G := graphGroup (V := V) upper
  groupG := inferInstance
  factorUpper := fun v => graphEval upper v
  factorLower := fun v => (link.isoPi v).comp (graphEval upper v)
  factorLower_eq := fun v => rfl

/-- The source units action on the graph group. -/
def linkedSourceAction (upper : FPrimeStrip V) (v : V) :
    graphGroup (V := V) upper →* MulAut ((upper.Mon v)ˣ) :=
  (upper.unitsAction v).comp (graphEval upper v)

/-- The lower target action on the graph group. -/
def linkedTargetAction (link : FPrimeStripEquiv upper lower) (v : V) :
    graphGroup (V := V) upper →* MulAut ((lower.Mon v)ˣ) :=
  (lower.unitsAction v).comp ((link.isoPi v).comp (graphEval upper v))

/-- Lower kappa representative on the linked graph group. -/
noncomputable def linkedKappaLower (link : FPrimeStripEquiv upper lower) (v : V) :
    TimesMuKummer.Isomorphism
      (linkedSourceAction (V := V) upper v)
      (linkedTargetAction (V := V) (upper := upper) (lower := lower) link v) where
  equiv := TimesMuQuotient.congr (Units.mapEquiv (link.isoMon v))
  equivariant := by
    intro g x
    obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective (U := (upper.Mon v)ˣ) x
    change TimesMuQuotient.congr (Units.mapEquiv (link.isoMon v))
        (TimesMuQuotient.action (linkedSourceAction (V := V) upper v) g
          (TimesMuQuotient.quotientMap u)) =
      TimesMuQuotient.action
        (linkedTargetAction (V := V) (upper := upper) (lower := lower) link v) g
        (TimesMuQuotient.congr (Units.mapEquiv (link.isoMon v))
          (TimesMuQuotient.quotientMap u))
    rw [TimesMuQuotient.action_quotientMap, TimesMuQuotient.congr_quotientMap,
      TimesMuQuotient.action_quotientMap, TimesMuQuotient.congr_quotientMap]
    exact congrArg TimesMuQuotient.quotientMap
      (FPrimeStripEquiv.unitsAction_compat link v (g v) u)
  invariantImage := by
    intro H
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (TimesMuKummer.mem_invariantImage_iff
        (linkedSourceAction (V := V) upper v) H y).mp hy with ⟨u, hu, rfl⟩
      refine (TimesMuKummer.mem_invariantImage_iff
        (linkedTargetAction (V := V) (upper := upper) (lower := lower) link v)
        H (TimesMuQuotient.congr (Units.mapEquiv (link.isoMon v))
          (TimesMuQuotient.quotientMap u))).mpr ?_
      refine ⟨Units.mapEquiv (link.isoMon v) u, ?_, rfl⟩
      intro h
      have hcompat := FPrimeStripEquiv.unitsAction_compat link v
        (h : graphGroup (V := V) upper) u
      have hfixed : (upper.unitsAction v) ((h : graphGroup (V := V) upper) v) u = u :=
        hu h
      rw [hfixed] at hcompat
      simpa using hcompat.symm
    · rintro ⟨y, hy, rfl⟩
      rcases (TimesMuKummer.mem_invariantImage_iff
        (linkedTargetAction (V := V) (upper := upper) (lower := lower) link v)
        H y).mp hy with ⟨w, hw, rfl⟩
      refine (TimesMuKummer.mem_invariantImage_iff
        (linkedSourceAction (V := V) upper v) H
        (TimesMuQuotient.congr (Units.mapEquiv (link.isoMon v)).symm
          (TimesMuQuotient.quotientMap w))).mpr ?_
      refine ⟨Units.mapEquiv (link.isoMon v).symm w, ?_, ?_⟩
      · intro h
        apply (Units.mapEquiv (link.isoMon v)).injective
        have hcompat := FPrimeStripEquiv.unitsAction_compat link v
          (h : graphGroup (V := V) upper)
          (Units.mapEquiv (link.isoMon v).symm w)
        rw [show Units.mapEquiv (link.isoMon v)
            (Units.mapEquiv (link.isoMon v).symm w) = w by simp] at hcompat
        rw [hw h] at hcompat
        exact hcompat
      · rw [TimesMuQuotient.congr_quotientMap]
        congr 1
        simp

/-- The actual linked kappa data from a strip link. -/
noncomputable def linkedKappaData (link : FPrimeStripEquiv upper lower) :
    MissingLinkedKappaData upper lower link where
  common := linkedCommonGroup link
  kappaLower := fun v => linkedKappaLower link v

/-- Actual linked kappa package for S00 -> S01. -/
noncomputable def linkedKappaS00S01 :
    MissingLinkedKappaData (S00 (I := I)) (S01 (I := I)) (linkS00S01 (I := I)) :=
  linkedKappaData (V := V) (linkS00S01 (I := I))

/-- Actual linked kappa package for S01 -> S11. -/
noncomputable def linkedKappaS01S11 :
    MissingLinkedKappaData (S01 (I := I)) (S11 (I := I)) (linkS01S11 (I := I)) :=
  linkedKappaData (V := V) (linkS01S11 (I := I))

/-- The actual linked common group factorization is the link image of the
upper factorization. -/
theorem linkedKappaData_factorLower
    (link : FPrimeStripEquiv upper lower) (v : V) :
    (linkedKappaData (V := V) link).common.factorLower v =
      (link.isoPi v).comp ((linkedKappaData (V := V) link).common.factorUpper v) :=
  (linkedKappaData (V := V) link).common.factorLower_eq v

/-- Exact construction status: the linked common group and lower kappa are
actual for every supplied strip equivalence, including the two source links. -/
theorem linkedKappaActual_status :
    (MissingLinkedKappaData (S00 (I := I)) (S01 (I := I))
        (linkS00S01 (I := I))) ∧
      (MissingLinkedKappaData (S01 (I := I)) (S11 (I := I))
        (linkS01S11 (I := I))) :=
  ⟨linkedKappaS00S01 (I := I), linkedKappaS01S11 (I := I)⟩

end LeanFormal.IUT.XiFPaper.LinkedKappaActualAdapted

end
