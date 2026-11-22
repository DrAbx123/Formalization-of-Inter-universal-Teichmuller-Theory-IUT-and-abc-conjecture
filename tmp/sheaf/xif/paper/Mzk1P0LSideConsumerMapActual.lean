/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LSideConsumerMapActual
structure ConsumerRow where
  oldConsumer : String
  nativeReplacement : String
  status : String
def consumerRows : List ConsumerRow :=
  [⟨"concreteC3Donor/concreteQCandidate q", "NativeQDonor.q / donorQReadout", "SWITCHED"⟩,
   ⟨"concrete L tensor block", "nativeLSideBlock (qVFamTensorBlock)", "SWITCHED"⟩,
   ⟨"concrete L theta readout", "nativeLSideThetaReadout", "SWITCHED"⟩,
   ⟨"S3137 L readout", "native L-side readout", "MIGRATING"⟩]
theorem consumerRows_length : consumerRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LSideConsumerMapActual
end
