import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

/-- Consumer: S1300 hull+det source gives the S1215 HDD local lattice with
rank and lattice agreement. -/
theorem S3128Stage1HDDConsumer_rank_lattice
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank ∧
      ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
        (D.toS1215 (I := I)).lattice o v = D.lattice o v :=
  ⟨rfl, fun o v => D.toS1215_lattice o v⟩

/-- Consumer: the S1300 lattice is the transported local-field hull. -/
theorem S3128Stage1HDDConsumer_lattice_eq_hull
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  D.toS1215_lattice_eq_hull o v

/-- Consumer: the actual frozen hull+det specification. -/
theorem S3128Stage1HDDConsumer_frozenSpec :
    HullDeterminantLogVolumeFrozenSpec :=
  s1385FrozenSpec_actual

#check S3128Stage1HDDConsumer_rank_lattice
#check S3128Stage1HDDConsumer_lattice_eq_hull
#check S3128Stage1HDDConsumer_frozenSpec
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual