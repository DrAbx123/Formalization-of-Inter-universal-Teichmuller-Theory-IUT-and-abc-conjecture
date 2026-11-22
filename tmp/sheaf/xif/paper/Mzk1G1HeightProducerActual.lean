import tmp.sheaf.xif.paper.Mzk1P7LargeImageCyclicActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1HeightProducerActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageCyclicActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- Actual G1 height producer data: P7 archimedean height data and the G1
Fermat cover. -/
structure G1HeightProducerData where
  p7Height : P7LargeImageCyclicData 0
  fermatCover : FermatCoverData ℂ

noncomputable def g1HeightProducerData : G1HeightProducerData where
  p7Height := p7LargeImageCyclicData 0
  fermatCover := fermatCoverData ℂ 1 (by norm_num)

theorem g1HeightProducerData_nonempty : Nonempty G1HeightProducerData :=
  ⟨g1HeightProducerData⟩

end LeanFormal.IUT.XiFPaper.G1HeightProducerActual
end
