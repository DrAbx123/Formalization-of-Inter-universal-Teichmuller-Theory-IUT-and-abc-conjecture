import tmp.sheaf.xif.paper.Mzk1PStarScaleActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1P58iInvariantsAlgorithmActual — computable invariant extraction for Prop 5.8(i)
(parameter-level)

STEP 0 prior-art: SourceLogShellCarrier (sourceLogShellStar), Mzk1PStarScaleActual (p* facts)
-> REUSE; this file gives the computable invariant record and extraction functions
(p, p*, p^f, [k:Q_p]=f*e, e, p^m) together with their correctness statements.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iInvariantsAlgorithmActual

open LeanFormal.IUT

/-- Parameter data for the Prop 5.8(i) invariants: residue characteristic p, residue degree
f, absolute ramification index e, and the p-th-root order exponent m. -/
structure LocalFieldInvariantsData where
  p : ℕ
  hp : p.Prime
  f : ℕ
  e : ℕ
  m : ℕ

/-- The extracted residue characteristic p. -/
def LocalFieldInvariantsData.residueChar (I : LocalFieldInvariantsData) : ℕ := I.p

/-- The extracted p* (p if p odd, p^2 if p = 2). -/
def LocalFieldInvariantsData.pStar (I : LocalFieldInvariantsData) : ℕ :=
  if I.p = 2 then I.p ^ 2 else I.p

/-- The extracted residue cardinality p^f. -/
def LocalFieldInvariantsData.residueCardinality (I : LocalFieldInvariantsData) : ℕ :=
  I.p ^ I.f

/-- The extracted absolute degree [k:Q_p] = f*e. -/
def LocalFieldInvariantsData.absoluteDegree (I : LocalFieldInvariantsData) : ℕ :=
  I.f * I.e

/-- The extracted absolute ramification index e. -/
def LocalFieldInvariantsData.ramificationIndex (I : LocalFieldInvariantsData) : ℕ := I.e

/-- The extracted order p^m of the p-th power roots of unity. -/
def LocalFieldInvariantsData.pthRootsOrder (I : LocalFieldInvariantsData) : ℕ :=
  I.p ^ I.m

/-- The extracted p* equals the paper/ tree p* (sourceLogShellStar). -/
theorem LocalFieldInvariantsData.pStar_eq_sourceLogShellStar
    (I : LocalFieldInvariantsData) : I.pStar = sourceLogShellStar I.p := by
  unfold LocalFieldInvariantsData.pStar sourceLogShellStar
  rcases I.hp.eq_two_or_odd with h | h
  · rw [h]
    decide
  · have h2 : I.p ≠ 2 := by
      intro hh
      rw [hh] at h
      norm_num at h
    simp [h2, h]

/-- The extracted residue cardinality is p^f. -/
theorem LocalFieldInvariantsData.residueCardinality_eq (I : LocalFieldInvariantsData) :
    I.residueCardinality = I.p ^ I.f := rfl

/-- The extracted absolute degree is f*e. -/
theorem LocalFieldInvariantsData.absoluteDegree_eq (I : LocalFieldInvariantsData) :
    I.absoluteDegree = I.f * I.e := rfl

/-- The extracted p-th-root order is p^m. -/
theorem LocalFieldInvariantsData.pthRootsOrder_eq (I : LocalFieldInvariantsData) :
    I.pthRootsOrder = I.p ^ I.m := rfl

/-- The calibration-model parameter data: p = 5, f = e = 1 (the concrete source model). -/
def calibrationInvariantsData : LocalFieldInvariantsData where
  p := 5
  hp := by decide
  f := 1
  e := 1
  m := 0

/-- The calibration-model p* is 5 (odd prime case). -/
theorem calibrationInvariantsData_pStar : calibrationInvariantsData.pStar = 5 := rfl

/-- Algorithm rows: (item, extraction, correctness). -/
def invariantsAlgorithmRows : List (String × String × String) :=
  [ ("residue characteristic p", "residueChar = p", "DEFINED"),
    ("p* = p if odd, p^2 if p = 2", "pStar; pStar_eq_sourceLogShellStar", "PROVED"),
    ("residue cardinality p^f", "residueCardinality; residueCardinality_eq", "DEFINED (rfl)"),
    ("absolute degree [k:Q_p] = f*e", "absoluteDegree; absoluteDegree_eq", "DEFINED (rfl)"),
    ("ramification index e", "ramificationIndex = e", "DEFINED"),
    ("p-th-root order p^m", "pthRootsOrder; pthRootsOrder_eq", "DEFINED (rfl)"),
    ("calibration model p=5,f=e=1", "calibrationInvariantsData; pStar = 5", "CONSTRUCTED/PROVED"),
    ("group-theoretic extraction algorithm", "not asserted", "NAMED (paper deep input)") ]

/-- The algorithm row record has eight rows. -/
theorem invariantsAlgorithmRows_length : invariantsAlgorithmRows.length = 8 := rfl

#check LocalFieldInvariantsData
#check LocalFieldInvariantsData.pStar_eq_sourceLogShellStar
#check LocalFieldInvariantsData.residueCardinality_eq
#check LocalFieldInvariantsData.absoluteDegree_eq
#check calibrationInvariantsData_pStar
#check invariantsAlgorithmRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iInvariantsAlgorithmActual
end
