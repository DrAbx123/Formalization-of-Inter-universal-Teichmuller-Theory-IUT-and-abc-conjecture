import tmp.sheaf.xif.paper.S3128Stage1HDDConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDAndSHEConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1HDDAndSHE_facts
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    (D.toS1215 (I := I)).rank = D.rank
      ∧ C.sheLocalization.expression v o =
          (actualSHEOutput I).bundle.localization v unitSection :=
  ⟨(S3128Stage1HDDConsumer_rank_lattice D).1,
    S3128Stage1SHECompositionConsumer_readout_unit I J C v o⟩

#check S3128Stage1HDDAndSHE_facts
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDAndSHEConsumerActual