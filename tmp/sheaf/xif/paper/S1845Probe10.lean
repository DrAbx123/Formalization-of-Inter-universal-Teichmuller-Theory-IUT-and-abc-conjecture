import tmp.sheaf.xif.paper.S1844PointSeparatedActual
import Mathlib.RingTheory.Etale.Pi
noncomputable section
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual

example : Algebra.Etale S1726CoordinateRing (S1726CoordinateRing × S1726CoordinateRing) := by infer_instance
#check RingHom.etale_iff
#check RingHom.etale_algebraMap
#check RingHom.finite_iff
#check RingHom.finite_algebraMap
#check Algebra.Etale.of_algEquiv
#check AlgEquiv.ofAlgHom
example : RingHom.Etale S1844diag := by
  rw [RingHom.etale_iff]
  -- goal?
  sorry
