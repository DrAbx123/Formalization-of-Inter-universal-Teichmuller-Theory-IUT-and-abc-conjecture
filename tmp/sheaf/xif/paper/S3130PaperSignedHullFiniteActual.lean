import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.S2030Direct312Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3130PaperSignedHullFiniteActual

open LeanFormal.IUT

/-- Batch A, fixed qualified input C: a paper-level signed hull datum
`PaperSignedHull X label`.  Its fields (ambient IQHullLogVolumeInterface,
procession/hull matching, normalized-average equality, average nonnegativity)
are exactly the source obligations; the input is fixed as a parameter and no
inhabitant is manufactured here. -/
structure BatchAQualifiedInput (X : Type u) (label : Type v) [Fintype label] where
  signedHull : PaperSignedHull X label

variable {X : Type u} {label : Type v} [Fintype label]
variable (C : PaperSignedHull X label)

/-- `H_C`: the paper hull object of the fixed input, as an actual set of the
ambient carrier. -/
def H_C_set : Set X :=
  C.ambient.hull

/-- `H_C`: the ambient normalized log-volume of the hull object. -/
def H_C : ENNReal :=
  C.ambient.logVolume C.ambient.hull

/-- Object identification: the hull carried by the paper datum is exactly
`H_C_set`, and its log-volume is exactly `H_C`. -/
theorem H_C_identification :
    C.ambient.logVolume (H_C_set (X := X) (label := label) C) = H_C C :=
  rfl

/-- Batch A: finiteness of the paper hull log-volume `H_C`, from the actual
paper compactness/Haar interface `ambient_hull_logVolume_lt_top`. -/
theorem H_C_lt_top : H_C C < ⊤ :=
  PaperSignedHull.ambient_hull_logVolume_lt_top C

/-- `H_C` is bounded by the normalized unit-region log-volume
(compactness/lambda-scaling half of Remark 3.9.5). -/
theorem H_C_le_unitRegion :
    H_C C <= C.ambient.logVolume C.ambient.unitRegion :=
  PaperSignedHull.ambient_hull_logVolume_le_unitRegion C

/-- `Q_C`: the paper signed quantity `-|log Theta|`, defined as the negative of
the ambient normalized hull log-volume. -/
def Q_C : Real :=
  C.signedHullLogVolume

/-- Sign/identification: `Q_C` is the negative of the normalized procession
average supplied by the fixed input. -/
theorem Q_C_eq_neg_average :
    Q_C C = -C.procession.average :=
  PaperSignedHull.signedHullLogVolume_eq_neg_average C

/-- `Q_C` is nonpositive. -/
theorem Q_C_nonpos : Q_C C <= 0 :=
  PaperSignedHull.signedHullLogVolume_nonpos C

/-- Batch A comparison: `Q_C` is bounded by the (real) normalized hull
log-volume `H_C.toReal`, because `Q_C = -average` and `average >= 0` while
`H_C.toReal = average` under the exact procession-normalization obligation. -/
theorem Q_C_le_H_C_toReal : Q_C C <= (H_C C).toReal := by
  have hH : H_C C = ENNReal.ofReal C.procession.average :=
    C.hull_logVolume_eq_average
  have havg : 0 <= C.procession.average :=
    C.average_nonneg
  rw [Q_C_eq_neg_average C, hH, ENNReal.toReal_ofReal havg]
  linarith

/-- Batch A package on the fixed qualified input: the hull object and its
log-volume, finiteness, unit-region bound, and `Q_C <= H_C.toReal`. -/
theorem BatchA_package :
    (C.ambient.logVolume (H_C_set (X := X) (label := label) C) = H_C C) ∧
      H_C C < ⊤ ∧
      H_C C <= C.ambient.logVolume C.ambient.unitRegion ∧
      Q_C C <= (H_C C).toReal :=
  ⟨H_C_identification (X := X) (label := label) C,
    H_C_lt_top C, H_C_le_unitRegion C, Q_C_le_H_C_toReal C⟩

/-- The same package from an explicitly bundled Batch-A input. -/
theorem BatchA_package_of_input
    (I : BatchAQualifiedInput X label) :
    (I.signedHull.ambient.logVolume (H_C_set I.signedHull) = H_C I.signedHull) ∧
      H_C I.signedHull < ⊤ ∧
      H_C I.signedHull <=
        I.signedHull.ambient.logVolume I.signedHull.ambient.unitRegion ∧
      Q_C I.signedHull <= (H_C I.signedHull).toReal :=
  BatchA_package (X := X) (label := label) I.signedHull

#check H_C_lt_top
#check Q_C_le_H_C_toReal
#check BatchA_package
#check BatchA_package_of_input

end LeanFormal.IUT.XiFPaper.S3130PaperSignedHullFiniteActual
end
