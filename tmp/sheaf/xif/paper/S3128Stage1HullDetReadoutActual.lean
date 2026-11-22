import tmp.sheaf.xif.paper.S1385HDDHullDetActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.SHEOutputActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HullDetReadoutActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

noncomputable def S3128Stage1HDDHullReadout (D : S1300HDDHullDetSource I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    Set (Fin D.rank → (oneColumnStructure).localField v) :=
  D.lattice o v

theorem S3128Stage1HDDHullReadout_eq_source
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    S3128Stage1HDDHullReadout D o v = D.lattice o v := rfl

theorem S3128Stage1HDDHullReadout_eq_hull
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    S3128Stage1HDDHullReadout D o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  D.toS1215_lattice_eq_hull o v

theorem S3128Stage1HDDDetReadout_spec :
    HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  s1385FrozenSpec_actual

#check S3128Stage1HDDHullReadout
#check S3128Stage1HDDHullReadout_eq_source
#check S3128Stage1HDDHullReadout_eq_hull
#check S3128Stage1HDDDetReadout_spec
end LeanFormal.IUT.XiFPaper.S3128Stage1HullDetReadoutActual