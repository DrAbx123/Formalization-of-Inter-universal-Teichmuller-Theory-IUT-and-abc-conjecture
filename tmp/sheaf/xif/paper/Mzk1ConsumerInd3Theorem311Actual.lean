import LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind3UpperSemiConstruction
import LeanFormal/IUT/IUTIII/Theorem311/SourceTheorem311Assembly

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerInd3Theorem311Actual — A476 real consumer theorems (Ind3 / Thm 3.11)

New conclusions combining existing donor theorems:

* Ind3 (`Ind3UpperSemiConstruction.lean:51/56/66/74/85/96`):
  the value form of every stage, the monotone stage-value inequality, and the
  joint (upper-semi ∧ sharp stage criterion) package;
* Theorem 3.11 assembly (`SourceTheorem311Assembly.lean:60/81/85/89`):
  the four recovered layer equalities as one conjunction, and the chained
  `assemble -> dependency_part_i` equality.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerInd3Theorem311Actual

open LeanFormal.IUT
open LeanFormal.IUT.Ind3UpperSemi
open LeanFormal.IUT.Theorem311Source

/-- **Ind3 value form consumer** (stage membership = explicit value). -/
theorem ind3_value_mem_iff (l : PrimeGeFive) (c : ProcessionChoice l)
    (n : Nat) (z : Real) :
    z ∈ Ind3UpperSemi.outputImageFamily l c n ↔
      z = thetaLogVolume l + ((c.upperSemiLevel + n : Nat) : Real) :=
  Ind3UpperSemi.outputImageFamily_value l c n z

/-- **Ind3 monotone stage-value consumer**: the explicit stage values are
monotone in the stage index. -/
theorem ind3_stage_value_monotone (l : PrimeGeFive) (c : ProcessionChoice l)
    {m n : Nat} (hmn : m ≤ n) :
    thetaLogVolume l + ((c.upperSemiLevel + m : Nat) : Real) ≤
      thetaLogVolume l + ((c.upperSemiLevel + n : Nat) : Real) := by
  have h := Ind3UpperSemi.normalizedLogVolume_ind3_le_of_le l c hmn
  simpa [normalizedLogVolume] using h

/-- **Ind3 joint law consumer**: the constructed stage family is upper-semi and
its stage-domination criterion is sharp at the same time. -/
theorem ind3_upperSemi_and_sharp (l : PrimeGeFive) (c : ProcessionChoice l) :
    IsUpperSemi (Ind3UpperSemi.outputImageFamily l c) ∧
      (∀ m n : Nat,
        Ind3UpperSemi.outputImageFamily l c m ≤
            Ind3UpperSemi.outputImageFamily l c n ↔ m ≤ n) :=
  ⟨Ind3UpperSemi.outputImageFamily_upper l c,
   fun m n => Ind3UpperSemi.outputImageFamily_le_iff l c m n⟩

/-- **Theorem 3.11 layer recovery consumer**: all four assembled layer
equalities hold jointly. -/
theorem theorem311_layers_recovered
    {I R P X Y : Type*}
    (W : SourceInternalWiring I R P X Y)
    (S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y) W)
    (B : SourceP1P2Bundle W S) (L : SourceTheorem311Layers B) :
    L.t1 = B.dependency.output.part_i ∧
      L.t2 = B.dependency.output.part_ii ∧
      L.t3 = B.dependency.output.part_iii ∧
      L.output = B.dependency.output :=
  ⟨L.t1_eq, L.t2_eq, L.t3_eq, L.output_eq⟩

/-- **Theorem 3.11 assembled t1 -> partI chain consumer**. -/
theorem theorem311_assemble_t1_to_partI
    {I R P X Y : Type*}
    (W : SourceInternalWiring I R P X Y)
    (S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y) W)
    (B : SourceP1P2Bundle W S) :
    (SourceTheorem311Layers.assemble B).t1 = partI R.input := by
  rw [SourceTheorem311Layers.t1_recovered (SourceTheorem311Layers.assemble B)]
  exact SourceTheorem311Layers.dependency_part_i B

#check theorem311_layers_recovered
#check ind3_upperSemi_and_sharp

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerInd3Theorem311Actual
end