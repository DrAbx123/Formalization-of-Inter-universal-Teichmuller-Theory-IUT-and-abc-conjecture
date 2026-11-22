import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerDownstreamActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

theorem S3128Stage1HDDConsumerDownstream_spec
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank ∧
      (∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
        (D.toS1215 (I := I)).lattice o v =
          (fun x : (i : Fin D.rank) → D.E i =>
            fun i => D.localEquiv v i (x i)) ''
          @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)) ∧
      HullDeterminantLogVolumeFrozenSpec :=
  ⟨(S3128Stage1HDDConsumer_rank_lattice D).1,
    fun o v => S3128Stage1HDDConsumer_lattice_eq_hull D o v,
    S3128Stage1HDDConsumer_frozenSpec⟩

theorem S3128Stage1HDDConsumerDownstream_lattice
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v = D.lattice o v :=
  (S3128Stage1HDDConsumer_rank_lattice D).2 o v

#check S3128Stage1HDDConsumerDownstream_spec
#check S3128Stage1HDDConsumerDownstream_lattice
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerDownstreamActual