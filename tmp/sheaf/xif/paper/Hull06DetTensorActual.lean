import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: matrixLogDet|HullDeterminantLogVolumeReduction|det tensor|O(-)|Ob3-3 -> hits LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean:123 HullDeterminantLogVolumeFrozenSpec, :153 frozenSpec_holds, :173 matrixLogDet, :179 matrixLogDet_mul_posDef, :187 matrixLogDet_smul_posDef, :197 matrixLogDet_kronecker_posDef -> REUSE (H5 det/lambda-O scaling laws; no re-proof).

# [Hull] 06: H5 det tensor bookkeeping (Remark 3.9.5(i) at the determinant level)

Corpus: IUT III, Remark 3.9.5(i) (hull = lambda*O), Step (xi-d)/(Ob3-3): the
determinant/log-volume bookkeeping of the weighted positive tensor powers and the
O(-)^{-1} normalization.  The tree already PROVES the determinant laws in
HullDeterminantLogVolumeReduction (matrixLogDet additive on posDef factors, the
lambda*O rescaling law with weight (card n) * log c, and the Kronecker tensor law).
This file re-exports them as the H5 det bookkeeping rows and records the remaining
O^x-stabilization / O(-)^{-1} normalization items (class B named rows, NOT proved).
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull06DetTensorActual

open LeanFormal.IUT

/-- The log-determinant of a real matrix (det/log-volume readout; reused). -/
noncomputable def hull06MatrixLogDet {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ℝ :=
  matrixLogDet A

/-- **lambda*O rescaling law at the determinant level** (Remark 3.9.5(i)):
rescaling A by c > 0 shifts the log-det by (card n) * log c, i.e. by the
dimension times the log of the hull scaling. -/
theorem hull06_det_scaling {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (c : ℝ) (hc : 0 < c) (hA : A.PosDef) :
    hull06MatrixLogDet (c • A) =
      (Fintype.card n : ℝ) * Real.log c + hull06MatrixLogDet A :=
  matrixLogDet_smul_posDef c hc hA

/-- PosDef multiplicativity of the log-det (reused). -/
theorem hull06_det_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    hull06MatrixLogDet (A * B) =
      hull06MatrixLogDet A + hull06MatrixLogDet B :=
  matrixLogDet_mul_posDef hA hB

/-- H5 bookkeeping rows: (item, tree anchor, status). -/
structure Hull06Row where
  item : String
  anchor : String
  status : String

/-- The H5 det tensor bookkeeping rows. -/
def hull06Rows : List Hull06Row :=
  [ { item := "det/lambda-O scaling law (Remark 3.9.5(i) at determinant level)",
      anchor := "HullDeterminantLogVolumeReduction:187 matrixLogDet_smul_posDef",
      status := "PROVED (reused: hull06_det_scaling)" }
  , { item := "det multiplicativity on posDef factors",
      anchor := "HullDeterminantLogVolumeReduction:179 matrixLogDet_mul_posDef",
      status := "PROVED (reused: hull06_det_mul)" }
  , { item := "det Kronecker tensor law (weighted tensor powers)",
      anchor := "HullDeterminantLogVolumeReduction:197 matrixLogDet_kronecker_posDef",
      status := "PROVED in tree (notation requires scoped Kronecker; not re-exported here)" }
  , { item := "HullDeterminantLogVolumeFrozenSpec (Step (xi-d) bookkeeping)",
      anchor := "HullDeterminantLogVolumeReduction:123/:153 hullDeterminantLogVolumeFrozenSpec_holds",
      status := "frozen spec (tree; not re-proved here)" }
  , { item := "O^x-stabilization of the hull",
      anchor := "none (class B named item; needs O^x-stabilized hull definition)",
      status := "GAP (named)" }
  , { item := "O(-)^{-1} normalization of the determinant line bundle",
      anchor := "none (class B named item)",
      status := "GAP (named)" }
  , { item := "Ob3-3 det/log-volume consistency with the packet log-shells",
      anchor := "HullDeterminantLogVolumeReduction:123 frozen spec + S3137 packet normalized log-volume",
      status := "tree-consistency interface; full bridge class B" } ]

/-- The H5 record has seven rows. -/
theorem hull06Rows_length : hull06Rows.length = 7 := rfl

#check hull06MatrixLogDet
#check hull06_det_scaling
#check hull06_det_mul
#check hull06Rows_length

end LeanFormal.IUT.XiFPaper.Hull06DetTensorActual