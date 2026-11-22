import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

/-- Consumer: the S1300 hull+det source carries actual determinant bookkeeping. -/
theorem S3128Stage1HDDDetReadoutConsumer_detBookkeeping
    (D : S1300HDDHullDetSource I) :
    Nonempty
      (DetTensorPowerLogVolumeBookkeeping
        (Set ((i : Fin D.rank) → D.E i))) :=
  ⟨D.detData⟩

/-- Consumer: the hull readout is the actual transported local-field hull. -/
theorem S3128Stage1HDDDetReadoutConsumer_hull
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  D.toS1215_lattice_eq_hull o v

/-- Consumer: rank is preserved by the S1300→S1215 readout. -/
theorem S3128Stage1HDDDetReadoutConsumer_rank
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank := rfl

/-- Consumer: actual frozen hull+det specification. -/
theorem S3128Stage1HDDDetReadoutConsumer_frozenSpec :
    HullDeterminantLogVolumeFrozenSpec :=
  s1385FrozenSpec_actual

#check S3128Stage1HDDDetReadoutConsumer_detBookkeeping
#check S3128Stage1HDDDetReadoutConsumer_hull
#check S3128Stage1HDDDetReadoutConsumer_rank
#check S3128Stage1HDDDetReadoutConsumer_frozenSpec
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual