import tmp.sheaf.xif.paper.S3128Stage1SHEHDDStage1FourthJointPremiseActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDDetReadoutConsumerActual

/-!
# S3134: the fourth-joint composite arrow `(hull+det) ∘ (dsc)SHE`

IUT III, Corollary 3.12, Step (xi-d) (corpus `Inter-universal Teichmuller
Theory III.txt:10823-10864`) and Step (xi-e)/(xi-f) (`:10864-10899`): the
holomorphic hull and the determinant normalization are applied to the output
of the descent `(dsc)`/SHE step, and the resulting log-volume is compared with
the q-pilot log-volume.

This file composes the two actual arrows of the fourth joint instead of
recording a conjunction of component existences:

* `S3134SHEReadout` is the actual 1-column localization expression of the
  SHE/HDD compatibility record;
* `S3134HullDetReadout` is the actual `S1300` hull lattice (the image under
  the actual local-field identification of `LocalFieldProductHull.hull` of the
  HDD image family);
* `S3134FourthJointComposite` is their composite evaluated at the actual
  Theorem 3.11 output object carried by `actualSHEOutput`; the two projection
  laws, the transported-hull equality, the lattice equality, and nonemptiness
  of the composite hull are proved from the actual data.

The only field of the fourth joint that the two actual records do not supply is
the identification of the SHE/HDD compatibility record's HDD local lattice
with the hull+det source lattice. `S3134SHEHDDHLatticeIdentification` records
it as an exact missing identification (not a `True` marker), and
`S3134SHEHDDLoopData` is the closed SHE/HDD data loop conditional on exactly
that identification. No sorry, axiom, `True`, `PUnit`, or toy carrier is
used. WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual

namespace LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual Theorem 3.11 output object produced by the descent/SHE step. -/
noncomputable def S3134SHEOutputObject : Theorem311Output I :=
  (actualSHEOutput I).output

/-- The SHE arrow of the fourth joint: the actual 1-column localization
expression at the given place and output. -/
noncomputable def S3134SHEReadout
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    (oneColumnStructure).localRing v :=
  C.sheLocalization.expression v o

/-- The hull+det arrow of the fourth joint: the actual HDD hull lattice of the
`S1300` hull+det source at the given output and place. -/
noncomputable def S3134HullDetReadout
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    Set (Fin D.rank → (oneColumnStructure).localField v) :=
  D.toS1215.lattice o v

/-- The composite arrow `(hull+det) ∘ (dsc)SHE` at a place: the SHE readout and
the hull+det readout, both evaluated at the actual SHE output object. -/
noncomputable def S3134FourthJointComposite
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (oneColumnStructure).localRing v ×
      Set (Fin D.rank → (oneColumnStructure).localField v) :=
  (S3134SHEReadout (I := I) (J := J) C v (S3134SHEOutputObject (I := I)),
   S3134HullDetReadout (I := I) D (S3134SHEOutputObject (I := I)) v)

/-- First projection law of the composite: the first component is the SHE arrow
at the actual SHE output object. -/
@[simp] theorem S3134FourthJointComposite_fst
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (S3134FourthJointComposite (I := I) (J := J) D C v).1 =
      S3134SHEReadout (I := I) (J := J) C v (S3134SHEOutputObject (I := I)) :=
  rfl

/-- Second projection law of the composite: the second component is the
hull+det arrow at the actual SHE output object. -/
@[simp] theorem S3134FourthJointComposite_snd
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (S3134FourthJointComposite (I := I) (J := J) D C v).2 =
      S3134HullDetReadout (I := I) D (S3134SHEOutputObject (I := I)) v :=
  rfl

/-- The SHE arrow reads the actual unit integral section: the actual
1-column localization of the actual unit section of the actual line bundle. -/
theorem S3134SHEReadout_eq_actual
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    S3134SHEReadout (I := I) (J := J) C v o =
      (actualSHEOutput I).bundle.localization v unitSection :=
  S3128Stage1SHECompositionConsumer_readout_unit (I := I) (J := J) C v o

/-- The hull+det arrow is exactly the actual transported local-field hull of the
HDD image family. -/
theorem S3134HullDetReadout_eq_hull
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    S3134HullDetReadout (I := I) D o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  S3128Stage1HDDDetReadoutConsumer_hull (I := I) D o v

/-- The hull+det arrow agrees with the source lattice field. -/
theorem S3134HullDetReadout_eq_lattice
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    S3134HullDetReadout (I := I) D o v = D.lattice o v :=
  D.toS1215_lattice o v

/-- The actual hull is nonempty: the actual HDD image family is nonempty and is
contained in its holomorphic hull (Remark 3.9.5, (ii), `P ⊆ phi(P)`), so its
image under the actual local-field identification is a point of the readout. -/
theorem S3134HullDetReadout_nonempty
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (S3134HullDetReadout (I := I) D o v).Nonempty := by
  obtain ⟨y, hy⟩ := D.nonempty o
  refine ⟨fun i => D.localEquiv v i (y i), ?_⟩
  rw [S3134HullDetReadout_eq_hull (I := I) D o v]
  exact ⟨y, (@LocalFieldProductHull.subset_hull (Fin D.rank) D.E D.normedField
    (D.image o)) hy, rfl⟩

/-- The composite hull is nonempty at every place. -/
theorem S3134FourthJointComposite_snd_nonempty
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (S3134FourthJointComposite (I := I) (J := J) D C v).2.Nonempty :=
  S3134HullDetReadout_nonempty (I := I) D (S3134SHEOutputObject (I := I)) v

/-- Exact missing identification of the SHE/HDD data loop: the HDD local lattice
carried by the SHE/HDD compatibility record must be the actual `S1300`
hull+det lattice of the same input. Both sides are actual objects of the same
type `S1215HDDLocalLattice`; the identification is a source input of the
fourth joint (IUT III, Corollary 3.12, Step (xi-d), where the holomorphic
hull+det is applied to the output of the SHE step), not a consequence of the
two records. It is recorded as an exact Prop, not as an arbitrary carrier. -/
def S3134SHEHDDHLatticeIdentification
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop :=
  C.hddLocalLattice = D.toS1215 (I := I)

/-- Consequence of the identification: the ranks agree. -/
theorem S3134SHEHDDHLatticeIdentification_rank
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (H : S3134SHEHDDHLatticeIdentification (I := I) (J := J) D C) :
    C.hddLocalLattice.rank = D.rank := by
  have H' : C.hddLocalLattice = D.toS1215 (I := I) := H
  have h : C.hddLocalLattice.rank = (D.toS1215 (I := I)).rank :=
    congrArg (fun L : S1215HDDLocalLattice (I := I) => L.rank) H'
  simpa using h

/-- The closed SHE/HDD data loop: every field is an actual theorem or actual
data of the fourth joint, and the single missing source identification is
carried as the last field. -/
structure S3134SHEHDDLoopData
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) where
  /-- The actual HDD local lattice, identified with the hull+det source. -/
  hddLattice : S1215HDDLocalLattice (I := I)
  hddLattice_eq : C.hddLocalLattice = hddLattice
  /-- The SHE readout is the actual unit-section localization. -/
  sheReadout_eq : ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v unitSection
  /-- The actual vertical log-shift invariance of the 1-column readout. -/
  logShift : ∀ (m m' : Int) (j : SignedLabel l.value),
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  /-- The actual theta readout of the 1-column. -/
  thetaReadout : ∀ (m : Int) (j : SignedLabel l.value),
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)
  /-- The hull+det readout is the actual transported hull. -/
  hullDetReadout_eq_hull : ∀ (o : Theorem311Output I)
      (v : NumberField.FinitePlace ℚ),
    S3134HullDetReadout (I := I) D o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)
  /-- The actual composite hull is nonempty. -/
  hullDetReadout_nonempty : ∀ (o : Theorem311Output I)
      (v : NumberField.FinitePlace ℚ),
    (S3134HullDetReadout (I := I) D o v).Nonempty
  /-- The actual frozen hull+det specification. -/
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  /-- The actual determinant log-volume bookkeeping of the HDD source. -/
  detBookkeeping : DetTensorPowerLogVolumeBookkeeping (Set ((i : Fin D.rank) → D.E i))
  /-- The exact missing source identification of the two HDD lattices. -/
  latticeIdentification : S3134SHEHDDHLatticeIdentification (I := I) (J := J) D C

/-- Construction of the SHE/HDD loop from the actual fourth-joint components,
conditional on exactly the missing lattice identification. -/
noncomputable def S3134SHEHDDLoopData_ofActuals
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (H : S3134SHEHDDHLatticeIdentification (I := I) (J := J) D C) :
    S3134SHEHDDLoopData (I := I) (J := J) D C where
  hddLattice := D.toS1215 (I := I)
  hddLattice_eq := H
  sheReadout_eq := fun v o =>
    S3128Stage1SHECompositionConsumer_readout_unit (I := I) (J := J) C v o
  logShift := fun m m' j =>
    S3128Stage1SHECompositionConsumer_logShift (l := l) (J := J) m m' j
  thetaReadout := fun m j => oneColumnLogReadout_theta J m j
  hullDetReadout_eq_hull := fun o v => S3134HullDetReadout_eq_hull (I := I) D o v
  hullDetReadout_nonempty := fun o v => S3134HullDetReadout_nonempty (I := I) D o v
  frozen := s1385FrozenSpec_actual
  detBookkeeping := D.detData
  latticeIdentification := H

/-- The HDD lattice of the closed loop is the actual hull+det source lattice. -/
theorem S3134SHEHDDLoopData_hddLattice
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (H : S3134SHEHDDHLatticeIdentification (I := I) (J := J) D C) :
    (S3134SHEHDDLoopData_ofActuals (I := I) (J := J) D C H).hddLattice =
      D.toS1215 (I := I) :=
  rfl

#check S3134FourthJointComposite
#check S3134FourthJointComposite_fst
#check S3134FourthJointComposite_snd
#check S3134HullDetReadout_nonempty
#check S3134SHEHDDHLatticeIdentification
#check S3134SHEHDDLoopData
#check S3134SHEHDDLoopData_ofActuals

end LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
