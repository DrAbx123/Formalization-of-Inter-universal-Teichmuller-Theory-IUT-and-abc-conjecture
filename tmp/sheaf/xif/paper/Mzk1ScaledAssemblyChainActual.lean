import tmp.sheaf.xif.paper.Mzk1StepXIContractAssemblyActual
import tmp.sheaf.xif.paper.Mzk1StepXIScalingActual

/-! Mainline: chain consumer combining contract assembly and positive rescaling
  (new composed conclusion). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledAssemblyChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingActual

theorem scaled_assembly_conclusion (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htth : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt)
    (k : ℝ) (hk : 0 < k) :
    Cor312Conclusion
      (scaleStepXIContract k hk
        (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt)) :=
  scaleStepXIContract_conclusion k hk
    (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt)

theorem scaled_assembly_ipl (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htth : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt)
    (k : ℝ) (hk : 0 < k) :
    (scaleStepXIContract k hk
      (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt)).ipl :=
  ipl

end LeanFormal.IUT.XiFPaper.Mzk1ScaledAssemblyChainActual