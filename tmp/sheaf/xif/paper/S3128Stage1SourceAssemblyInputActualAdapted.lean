import tmp.sheaf.xif.paper.S3128SHEHDDInterfaceActual
import tmp.sheaf.xif.paper.S3128HDDPremiseActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionActual
import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HullDetReadoutActual
import tmp.sheaf.xif.paper.S3128Stage1HDDDetReadoutConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1HDDReadoutSpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
open LeanFormal.IUT.XiFPaper.S3128HDDPremiseActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HullDetReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDDetReadoutConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutSpecActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SourceAssemblyInputActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Source-faithful Stage1 input assembly, field by field, all supplied by
the actual U3/U12/U13/U16/U19/U21 components.  This is the Stage1 half of
the data needed by `SourceTheorem311Assembly`; the remaining H1/H2/LGP/
Kummer/permutation boundaries are recorded as the explicit gap below. -/
structure S3128Stage1SourceAssemblyInput
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  hdd_source : S1300HDDHullDetSource I
  hdd_rank : (D.toS1215 (I := I)).rank = D.rank
  hdd_lattice :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (D.toS1215 (I := I)).lattice o v = D.lattice o v
  hdd_frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  hdd_readout_spec : S3128Stage1HDDReadoutSpec (I := I) D
  hdd_det :
    Nonempty
      (DetTensorPowerLogVolumeBookkeeping
        (Set ((i : Fin D.rank) → D.E i)))
  she_composition : S3128Stage1SHECompositionPremise (J := J)
  she_readout :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
  fourth_joint : S3128Stage1SHEHDDFourthJointPremise (I := I) (J := J) D

theorem S3128Stage1SourceAssemblyInput_ofActuals
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SourceAssemblyInput (I := I) (J := J) D C :=
  { hdd_source := D
    hdd_rank := (S3128Stage1HDDConsumer_rank_lattice D).1
    hdd_lattice := fun o v => (S3128Stage1HDDConsumer_rank_lattice D).2 o v
    hdd_frozen := S3128Stage1HDDDetReadout_spec
    hdd_readout_spec := S3128Stage1HDDReadoutSpec_ofSource (I := I) D
    hdd_det := S3128Stage1HDDDetReadoutConsumer_detBookkeeping D
    she_composition := S3128Stage1SHECompositionPremise_holds (J := J)
    she_readout := fun v o =>
      S3128Stage1SHECompositionConsumer_readout_unit I J C v o
    fourth_joint := S3128Stage1SHEHDDFourthJointPremise_holds (I := I) (J := J) D }

#check S3128Stage1SourceAssemblyInput
#check S3128Stage1SourceAssemblyInput_ofActuals
end LeanFormal.IUT.XiFPaper.S3128Stage1SourceAssemblyInputActualAdapted