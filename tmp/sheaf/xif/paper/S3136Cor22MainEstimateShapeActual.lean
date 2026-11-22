import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Stage-4 host: Corollary 2.2, (ii) main-estimate shape (definitional)

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt,
Corollary 2.2, (ii) p.2426-2444: log(q-forall(-)) <= H_unif * eps_d^(-3) *
d^(4+eps_d) + H_K on Exc_d, with H_unif independent of K_V and H_K depending on
K_V. (Theorem 1.10 is the input; the estimate is class B.)

CONSUMER: mainline's Cor 2.2 statement slot. Definitional shape only; no estimate
is claimed.

LABEL: statement shape (class A definition of the class B target). Registry frozen;
new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136Cor22MainEstimateShapeActual

/-- The Cor 2.2 (ii) estimate shape: for all points in the exceptional set, the
log(q-forall) function is bounded by H_unif * eps_d^(-3) * d^(4+eps_d) + H_K. -/
def LGPCor22MainEstimateShape {α : Type*} (f : α → ℝ) (H_unif eps_d : ℝ)
    (d : ℕ) (H_K : ℝ) (exc : Set α) : Prop :=
  ∀ x ∈ exc, f x ≤ H_unif * (eps_d ^ (-3 : ℝ)) * ((d : ℝ) ^ (4 + eps_d)) + H_K

/-- The exceptional set is a finite subset of X(Q)<=d (Cor 2.2, (ii) p.2435-2446). -/
def LGPExcSetShape {α : Type*} (exc : Set α) (fiberBelow : α → ℕ → Prop) : Prop :=
  Set.Finite exc

#check LGPCor22MainEstimateShape
#check LGPExcSetShape

end LeanFormal.IUT.XiFPaper.S3136Cor22MainEstimateShapeActual