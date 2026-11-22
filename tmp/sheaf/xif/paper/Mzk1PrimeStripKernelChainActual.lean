/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PrimeStripValueKernelActual
import tmp.sheaf.xif.paper.Mzk1PrimeStripExponentActual

/-! # Chain bridge: value-kernel of elementary exponent operations -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripValueKernelActual

open LeanFormal.IUT.XiFPaper.PrimeStripExponentActual

variable {ι : Type*} [DecidableEq ι]

theorem evKernelIn_evZero (s : Finset ι) :
    evKernelIn s (evZero : ExpVec ι) = s := by
  ext i
  simp [evKernelIn, evZero]

theorem evKernelIn_neg (s : Finset ι) (f : ι → ℤ) :
    evKernelIn s (fun i => -f i) = evKernelIn s f := by
  ext i
  simp [evKernelIn]

theorem evKernelIn_neg_evNeg (s : Finset ι) (f : ExpVec ι) :
    evKernelIn s (fun i => -(f i)) = evKernelIn s f := evKernelIn_neg s f

theorem evKernelIn_empty_eq (s : Finset ι) :
    evKernelIn s (fun _ => (0 : ℤ)) = s := by
  ext i
  simp [evKernelIn]

end LeanFormal.IUT.XiFPaper.PrimeStripValueKernelActual
