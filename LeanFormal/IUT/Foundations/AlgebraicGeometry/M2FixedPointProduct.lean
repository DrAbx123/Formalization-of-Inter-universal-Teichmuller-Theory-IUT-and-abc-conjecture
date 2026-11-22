import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCasePiFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseFixedPointsTransport
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Abstract fixed-point product

If a `G`-equivariant `S`-algebra equivalence identifies `B` with a finite
product of `S`-algebras `T A`, then the fixed points of `B` are the product of
the fixed points of the `T A`.  This packages the final product step of the
global M2 assembly, independently of the concrete CRT construction.
-/
namespace ABCBridge.M2FixedPointProduct

universe u v

variable {S : Type u} [CommRing S] {B : Type u} [CommRing B] [Algebra S B]
  {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G S B]
  {κ : Type v} [Fintype κ] (T : κ → Type u)
  [∀ k, CommRing (T k)] [∀ k, Algebra S (T k)]
  [∀ k, MulSemiringAction G (T k)] [∀ k, SMulCommClass G S (T k)]

section ProductAction

local instance : MulSemiringAction G (∀ k, T k) :=
  SplitCasePiFixedPoints.piMulSemiringAction (T := T)

local instance : SMulCommClass G S (∀ k, T k) :=
  SplitCasePiFixedPoints.piSMulCommClass (T := T)

/-- Abstract fixed-point product along a `G`-equivariant algebra equivalence. -/
noncomputable def fixedPointProductAlgEquiv
    (e : B ≃ₐ[S] (∀ k, T k))
    (he : ∀ (g : G) (b : B), e (g • b) = g • e b) :
    FixedPoints.subalgebra S B G ≃ₐ[S]
      ∀ k, FixedPoints.subalgebra S (T k) G :=
  (SplitCaseFixedPointsTransport.fixedPointsAlgEquivOfEquiv e he).trans
    (SplitCasePiFixedPoints.fixedPointsPiAlgEquiv (S := S) (G := G) (T := T))

end ProductAction

end ABCBridge.M2FixedPointProduct