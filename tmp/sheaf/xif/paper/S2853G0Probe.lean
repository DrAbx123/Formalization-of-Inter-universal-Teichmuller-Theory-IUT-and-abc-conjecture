import tmp.sheaf.xif.paper.S2853ChartYNegationActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
noncomputable section
variable (K : Type) [Field K]
set_option maxHeartbeats 8000000
example : S2853G0Poly K (E37ChartYPolynomial K) = 0 := by
  rw [E37ChartYPolynomial]
  simp only [map_sub, map_pow, map_mul, map_add, S2853_hX0, S2853_hX1]
  ring_nf