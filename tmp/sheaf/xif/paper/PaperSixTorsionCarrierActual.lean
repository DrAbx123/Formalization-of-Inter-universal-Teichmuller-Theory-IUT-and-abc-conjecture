import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import LeanFormal.IUT.IUTII.Kummer.KummerGaloisClass
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual roots-of-unity six-slot torsion carrier

The frozen NativeSourceTorsionGaps.torsionLabel has domain
Multiplicative (LTorsion l), which has l^2 elements and cannot be a six-slot
labeling. This file constructs the actual six-roots-of-unity carrier in the
algebraic closure of the source base field:

  PaperSixTorsionCarrier T := rootsOfUnity 6 (AlgebraicClosure T.arithmetic.F).

This is an actual group. A six-slot labeling by Fin 6 is not constructed from
the frozen source data; it is recorded as the exact missing source object
PaperSixTorsionSlotLabel, rather than using a constant or l^2 label.

A corrected torsion-gap record with this actual carrier is supplied
conditionally on the missing six-slot label and the two source conditions.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperSixTorsionCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual six-roots-of-unity carrier in the algebraic closure of the source
base field. -/
abbrev PaperSixTorsionCarrier : Type :=
  rootsOfUnity 6 (AlgebraicClosure T.arithmetic.F)

/-- The actual group structure on the roots-of-unity carrier. -/
instance paperSixTorsionCarrierGroup : Group (PaperSixTorsionCarrier T) :=
  inferInstance

/-- A chosen primitive sixth root in the algebraic closure. -/
noncomputable def sixPrimitiveRootUnit : (AlgebraicClosure T.arithmetic.F)ˣ :=
  let h := Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure T.arithmetic.F) 6)
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure T.arithmetic.F) 6)).isUnit
    (by norm_num : 6 ≠ 0) |>.unit

/-- The chosen primitive root as a six-roots-of-unity element. -/
noncomputable def sixPrimitiveRoot : PaperSixTorsionCarrier T :=
  let h := Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure T.arithmetic.F) 6)
  let hζ := Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure T.arithmetic.F) 6)
  hζ.toRootsOfUnity

/-- The chosen unit is primitive of order six. -/
theorem sixPrimitiveRootUnit_isPrimitive :
    IsPrimitiveRoot (sixPrimitiveRootUnit T) 6 := by
  unfold sixPrimitiveRootUnit
  exact IsPrimitiveRoot.isUnit_unit (by norm_num : 6 ≠ 0)
    (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure T.arithmetic.F) 6))

/-- The actual six-slot label: every sixth root of unity is a unique power of
the chosen primitive root; the exponent is returned as an element of Fin 6. -/
noncomputable def paperSixTorsionLabel
    (x : PaperSixTorsionCarrier T) : Fin 6 :=
  let hx : (x : (AlgebraicClosure T.arithmetic.F)ˣ) ∈
      rootsOfUnity 6 (AlgebraicClosure T.arithmetic.F) := x.property
  let e := Classical.choose
    (sixPrimitiveRootUnit_isPrimitive T |>.eq_pow_of_mem_rootsOfUnity hx)
  ⟨e, (Classical.choose_spec
    (sixPrimitiveRootUnit_isPrimitive T |>.eq_pow_of_mem_rootsOfUnity hx)).1⟩

/-- The six-slot label is surjective. -/
theorem paperSixTorsionLabel_surjective :
    Function.Surjective (paperSixTorsionLabel T) := by
  intro k
  refine ⟨sixPrimitiveRoot T ^ (k : Nat), ?_⟩
  apply Fin.ext
  change (Classical.choose
    (sixPrimitiveRootUnit_isPrimitive T |>.eq_pow_of_mem_rootsOfUnity
      ((sixPrimitiveRoot T ^ (k : Nat)).property)) : Nat) = k
  have hspec := Classical.choose_spec
    (sixPrimitiveRootUnit_isPrimitive T |>.eq_pow_of_mem_rootsOfUnity
      ((sixPrimitiveRoot T ^ (k : Nat)).property))
  have hroot : ((sixPrimitiveRoot T : PaperSixTorsionCarrier T) :
      (AlgebraicClosure T.arithmetic.F)ˣ) = sixPrimitiveRootUnit T := by
    apply Units.ext
    simp [sixPrimitiveRoot, sixPrimitiveRootUnit, rootsOfUnity.coe_mkOfPowEq,
      IsPrimitiveRoot.toRootsOfUnity]
  have hpower : (sixPrimitiveRootUnit T) ^
      (Classical.choose
        (sixPrimitiveRootUnit_isPrimitive T |>.eq_pow_of_mem_rootsOfUnity
          ((sixPrimitiveRoot T ^ (k : Nat)).property))) =
      (sixPrimitiveRootUnit T) ^ (k : Nat) := by
    simpa [hroot] using hspec.2
  have hi := (sixPrimitiveRootUnit_isPrimitive T).pow_inj
    hspec.1 k.isLt hpower
  exact hi

/-- A six-slot labeling of the actual roots-of-unity carrier. The actual label
constructed above fills it; the label is not constant and is not the l^2-valued
l-torsion label. -/
structure PaperSixTorsionSlotLabel where
  label : PaperSixTorsionCarrier T → Fin 6
  label_surjective : Function.Surjective label

/-- The actual six-slot labeling constructed from the chosen primitive root. -/
noncomputable def paperSixTorsionSlotLabel : PaperSixTorsionSlotLabel T where
  label := paperSixTorsionLabel T
  label_surjective := paperSixTorsionLabel_surjective T

def PaperSixTorsionSlotLabelGap : Prop :=
  Nonempty (PaperSixTorsionSlotLabel T)

/-- The exact labeling gap is now inhabited by the actual primitive-root label. -/
theorem paperSixTorsionSlotLabelGap_holds :
    PaperSixTorsionSlotLabelGap (l := l) T :=
  ⟨paperSixTorsionSlotLabel T⟩



/-- Corrected torsion-gap record using the actual six-roots-of-unity carrier. -/
structure PaperNativeSourceTorsionGaps
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB) where
  torsionLabel : PaperSixTorsionCarrier T → Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- Conditional corrected torsion-gap data from the exact six-slot label. -/
noncomputable def paperNativeSourceTorsionGaps
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB)
    (L : PaperSixTorsionSlotLabel T)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent)
    (lTorsionCompatible : Prop)
    (lTorsionCompatible_proved : lTorsionCompatible) :
    PaperNativeSourceTorsionGaps (l := l) T D where
  torsionLabel := L.label
  sixTorsionIndependent := sixTorsionIndependent
  sixTorsionIndependent_proved := sixTorsionIndependent_proved
  lTorsionCompatible := lTorsionCompatible
  lTorsionCompatible_proved := lTorsionCompatible_proved

/-- The corrected carrier is the actual roots-of-unity carrier, not the l-torsion
group. -/
theorem paperNativeSourceTorsionGaps_carrier
    (D : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB)
    (L : PaperSixTorsionSlotLabel T)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent)
    (lTorsionCompatible : Prop)
    (lTorsionCompatible_proved : lTorsionCompatible) :
    (paperNativeSourceTorsionGaps (l := l) T D L sixTorsionIndependent
      sixTorsionIndependent_proved lTorsionCompatible lTorsionCompatible_proved).torsionLabel =
      L.label :=
  rfl

end LeanFormal.IUT.XiFPaper.PaperSixTorsionCarrierActual

end
