import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
set_option autoImplicit false
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
universe u v uv ua upi umon ui

def S3128Stage1SHEHDDFourthJointPremise
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V : Type uv}
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : S1300HDDHullDetSource I) : Prop :=
  (∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (D.toS1215 (I := I)).lattice o v = D.lattice o v) ∧
    HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} ∧
    (∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j))

theorem S3128Stage1SHEHDDFourthJointPremise_holds
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V : Type uv}
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : S1300HDDHullDetSource I) :
    S3128Stage1SHEHDDFourthJointPremise I J D := by
  refine ⟨fun o v => D.toS1215_lattice o v, s1385FrozenSpec_actual, ?_⟩
  intro m m' j
  exact s1215LogShiftReadoutCompat_actual (J := J) m m' j

noncomputable def S3128Stage1HDDLocalLattice
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    (D : S1300HDDHullDetSource I) : S1215HDDLocalLattice (I := I) :=
  D.toS1215

theorem S3128Stage1HDDLocalLattice_lattice
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    (D : S1300HDDHullDetSource I) (o : Theorem311Output I)
    (v : NumberField.FinitePlace ℚ) :
    (S3128Stage1HDDLocalLattice I D).lattice o v = D.lattice o v :=
  D.toS1215_lattice o v

#check S3128Stage1SHEHDDFourthJointPremise
#check S3128Stage1SHEHDDFourthJointPremise_holds
#check S3128Stage1HDDLocalLattice
#check S3128Stage1HDDLocalLattice_lattice
end LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual