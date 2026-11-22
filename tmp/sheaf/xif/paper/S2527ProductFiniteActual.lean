import Mathlib.RingTheory.Etale.Finite

noncomputable section
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2527ProductFiniteActual
universe u
variable (R : Type u) [CommRing R]

theorem S2527_prod_finite (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Finite R B] :
    Module.Finite R (A × B) := by infer_instance

#check S2527_prod_finite
#print axioms S2527_prod_finite
end LeanFormal.IUT.XiFPaper.S2527ProductFiniteActual
end