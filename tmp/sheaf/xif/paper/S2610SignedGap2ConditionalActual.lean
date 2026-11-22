import tmp.sheaf.xif.paper.S2609SignedGapPartsActual

noncomputable section
open LeanFormal.IUT
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2610SignedGap2ConditionalActual

universe u
theorem signedGap2_condition {X : Type u}
    (region scaledUnit singleton : Nat -> Nat -> Nat -> Set X)
    (hull : Set X) (logVolume : Set X -> ENNReal)
    {eps D0 D1 : Real} (hD0 : 0 <= D0) (hhullfin : logVolume hull < ⊤)
    (hsplit : forall a b c : Nat, IsABCTriple a b c ->
      logVolume (region a b c) <=
        logVolume (scaledUnit a b c) + logVolume (singleton a b c))
    (hunitScaled : forall a b c : Nat, IsABCTriple a b c ->
      logVolume (scaledUnit a b c) <= logVolume hull + ENNReal.ofReal D0)
    (hptfin : forall a b c : Nat, IsABCTriple a b c ->
      logVolume (singleton a b c) < ⊤)
    (hpoint : forall a b c : Nat, IsABCTriple a b c ->
      (logVolume (singleton a b c)).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1) :
    forall a b c : Nat, IsABCTriple a b c ->
      (logVolume (region a b c)).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          (logVolume hull).toReal + (D0 + D1) := by
  intro a b c habc
  have hunit' : logVolume (scaledUnit a b c) <=
      logVolume hull + ENNReal.ofReal D0 := hunitScaled a b c habc
  have hsum : logVolume (region a b c) <=
      (logVolume hull + ENNReal.ofReal D0) + logVolume (singleton a b c) :=
    le_trans (hsplit a b c habc) (add_le_add hunit' le_rfl)
  have hfin : logVolume hull + ENNReal.ofReal D0 ≠ ⊤ :=
    ne_of_lt (ENNReal.add_lt_top.mpr ⟨hhullfin, ENNReal.ofReal_lt_top⟩)
  have hsumFin : (logVolume hull + ENNReal.ofReal D0) +
      logVolume (singleton a b c) ≠ ⊤ :=
    ne_of_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
      ⟨hhullfin, ENNReal.ofReal_lt_top⟩, hptfin a b c habc⟩)
  have hreal : (logVolume (region a b c)).toReal <=
      ((logVolume hull + ENNReal.ofReal D0) +
        logVolume (singleton a b c)).toReal :=
    ENNReal.toReal_mono hsumFin hsum
  have htoReal : ((logVolume hull + ENNReal.ofReal D0) +
      logVolume (singleton a b c)).toReal =
      (logVolume hull).toReal + D0 + (logVolume (singleton a b c)).toReal := by
    simp only [ENNReal.toReal_add hfin (ne_of_lt (hptfin a b c habc)),
      ENNReal.toReal_add (ne_of_lt hhullfin) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hD0]
  rw [htoReal] at hreal
  have hpt := hpoint a b c habc
  linarith

#check signedGap2_condition
#print axioms signedGap2_condition

end LeanFormal.IUT.XiFPaper.S2610SignedGap2ConditionalActual
end