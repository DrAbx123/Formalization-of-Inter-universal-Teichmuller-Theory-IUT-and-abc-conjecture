import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
namespace LeanFormal.IUT.XiFPaper.S3128S1300InterfaceActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

/-- S1300 source produces the exact S1215 local lattice. -/
theorem S3128S1300_toS1215_lattice
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v = D.lattice o v := rfl

/-- S1300 local lattice is the actual transported local-field hull. -/
theorem S3128S1300_lattice_eq_hull
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  D.toS1215_lattice_eq_hull o v

#check S3128S1300_toS1215_lattice
#check S3128S1300_lattice_eq_hull
end LeanFormal.IUT.XiFPaper.S3128S1300InterfaceActual