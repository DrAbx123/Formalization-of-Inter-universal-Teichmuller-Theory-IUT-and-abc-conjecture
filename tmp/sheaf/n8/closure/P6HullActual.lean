import tmp.sheaf.n8.closure.P6Hull
import tmp.sheaf.n8.closure.C7SourceU
import Mathlib

/-!
# P6 actual hull setup from source U and sourceHolomorphicHull

The source family Alpha is the actual C4 witness family, R_alpha is the
singleton source output, U is the actual C4 output region, and the paper hull
operator is built from the actual sourceHolomorphicHull (not canonicalHull).

The actual Stp4 admissibility predicate Adm_out is NOT constructed here: it is
the exact missing donor ActualP6AdmOutData, with one named sorry.  No free Set
or arbitrary subset predicate is used; adm_out is constrained by source-U
membership and by admissibility of the source hull.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6HullActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.C7SourceU
open LeanFormal.IUT.N8Closure.P6Hull

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- The actual source carrier for P6 regions. -/
abbrev SourceCarrier : Type _ := I.ThetaPilotPoint D.place.v

/-- Alpha is the actual C4 witness family. -/
abbrev SourceAlpha : Type _ := D.Witness n x

/-- R_alpha is the actual source output witness singleton. -/
def sourceR (w : SourceAlpha (D := D) n x) : Set (SourceCarrier (D := D)) :=
  {D.witnessOutput w}

/-- The union of the actual R_alpha is exactly the actual C4 output region U. -/
theorem sourceUnion_eq_sourceU :
    (⋃ w : SourceAlpha (D := D) n x, sourceR (D := D) n x w) = D.U n x := by
  rw [D.U_eq_range]
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact Set.mem_iUnion.mpr ⟨w, by simp [sourceR]⟩

/-- The actual paper hull H = sourceHolomorphicHull (not canonicalHull). -/
def sourcePaperHull : Set (SourceCarrier (D := D)) :=
  I.sourceHolomorphicHull D.place.v D.place.R n

/-- The actual paper hull operator: S ↦ S ∪ H_source.  It uses the actual
source hull; it is not a free hull parameter. -/
def sourceHullOp : PaperHullOperator (SourceCarrier (D := D)) where
  hull S := S ∪ sourcePaperHull (D := D) n
  extensive S := Set.subset_union_left
  monotone hST := Set.union_subset_union hST (subset_rfl)
  idempotent S := by
    ext y
    simp [Set.union_assoc]

/-- The exact missing actual Stp4 admissibility data.  The predicate is not
free: it is required to contain every source output singleton and the actual
source hull. -/
structure ActualP6AdmOutData where
  adm_out : Set (SourceCarrier (D := D)) → Prop
  sourceR_admissible : ∀ w : SourceAlpha (D := D) n x,
    adm_out (sourceR (D := D) n x w)
  sourceHull_admissible : adm_out (sourcePaperHull (D := D) n)

/-- The actual P6HullSetup built from the actual source U/source hull and a
supplied Stp4 admissibility predicate. -/
def actualP6HullSetup (A : ActualP6AdmOutData (D := D) n x) : P6HullSetup where
  X := SourceCarrier (D := D)
  Alpha := SourceAlpha (D := D) n x
  R := sourceR (D := D) n x
  adm_out := A.adm_out
  paperHullOp := sourceHullOp (D := D) n
  paperHull := sourcePaperHull (D := D) n
  paperHull_eq := by
    rw [sourceUnion_eq_sourceU]
    ext y
    constructor
    · intro hy
      exact Set.mem_union_right _ hy
    · intro hy
      rcases hy with hyU | hyH
      · exact sourceU_subset_sourceHolomorphicHull (D := D) n x hyU
      · exact hyH

/-- The actual setup has U equal to the actual C4 output region. -/
theorem actualP6HullSetup_U_eq (A : ActualP6AdmOutData (D := D) n x) :
    (actualP6HullSetup (D := D) n x A).U = D.U n x :=
  sourceUnion_eq_sourceU (D := D) n x

/-- The actual setup has H equal to the actual source holomorphic hull. -/
theorem actualP6HullSetup_H_eq (A : ActualP6AdmOutData (D := D) n x) :
    (actualP6HullSetup (D := D) n x A).H = sourcePaperHull (D := D) n :=
  rfl

end LeanFormal.IUT.N8Closure.P6HullActual
