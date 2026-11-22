import tmp.sheaf.xif.paper.S2869Z2CoherentDataActual
import tmp.sheaf.xif.paper.S2876CorrectedA6CoreActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2869Z2CoherentDataActual
open LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2878DInputActual

/-- D only needs coherent Z/2 data; all other A6/D6 inputs are already
packaged upstream. -/
structure DInput (F : Type*) [Field F] (X : Iut.HyperbolicOrbicurve F) where
  coherent : Z2CoherentData (F := F) X

noncomputable def DInput.ofCoherent {F : Type*} [Field F]
    {X : Iut.HyperbolicOrbicurve F} (c : Z2CoherentData (F := F) X) :
    DInput F X :=
  ⟨c⟩

noncomputable def DInput.coherentData {F : Type*} [Field F]
    {X : Iut.HyperbolicOrbicurve F} (D : DInput F X) :
    Z2CoherentData (F := F) X :=
  D.coherent

theorem DInput.z2_only {F : Type*} [Field F]
    {X : Iut.HyperbolicOrbicurve F} (D : DInput F X) :
    Nonempty (Z2CoherentData (F := F) X) :=
  ⟨D.coherent⟩

#check DInput
#check DInput.ofCoherent
#check DInput.coherentData
#check DInput.z2_only

end LeanFormal.IUT.XiFPaper.S2878DInputActual
end
