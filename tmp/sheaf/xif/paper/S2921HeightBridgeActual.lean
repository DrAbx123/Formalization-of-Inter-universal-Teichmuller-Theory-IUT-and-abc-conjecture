import tmp.sheaf.xif.paper.S2920ThetaLinkHeight
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import tmp.sheaf.xif.paper.S2780LineBundleABCBridgeActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2920ThetaLinkHeight
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual

/-- Actual candidate for D: log of the local degree [F : Fmod] (the
different/local-degree term is represented by the field degree). -/
noncomputable def S2921D : Real :=
  Real.log ((Module.finrank S2847A6.Fmod S2847A6.F : Nat) : Real)

/-- Actual candidate for Q at an ABC triple: the q-pilot extended
line-bundle log-volume. -/
noncomputable def S2921Q (a b c : Nat) : Real :=
  S2736QPilotLineBundleLogVolume (l := S2771FiveLabel)
    (S2752J S2771FiveLabel a b c)

/-- Actual candidate for S at an ABC triple: log of the support ideal norm. -/
noncomputable def S2921S (a b c : Nat) : Real :=
  Real.log ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : Real)

/-- Actual candidate for T at an ABC triple: l*_mod times log support. -/
noncomputable def S2921T (a b c : Nat) : Real :=
  (S2771FiveLabel.value : Real) * S2921S a b c

theorem S2921_hweightvol_candidate (a b c : Nat) (habc : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) ≤ S2921Q a b c := by
  simpa [S2921Q] using S2752_hweightvol S2771FiveLabel a b c habc

theorem S2921Q_eq_regionVolume (a b c : Nat) :
    S2921Q a b c = S2780RegionVolume a b c := rfl

theorem S2921D_nonneg : 0 ≤ S2921D := by
  unfold S2921D
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    have : Module.finrank S2847A6.Fmod S2847A6.F ≠ 0 := Module.finrank_pos.ne'
    exact this)

/-- Exact pointwise target using the actual candidates. -/
def S2921HeightLeProcessionPointwise (n : Nat) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcJInvariant a b c) ≤
      (1 / (n : Real)) *
        ∑ j ∈ Icc 1 n,
          LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
            (2 * (n : Real) + 1) S2921D (S2921Q a b c) (S2921S a b c) (S2921T a b c) j

/-!
## First error / exact mismatch

The candidates above are actual, but they are triple-dependent:
Q = S2736QPilotLineBundleLogVolume (S2752J a b c),
S = log absNorm (S2752J a b c),
T = l*_mod * S.

S2920HeightLeProcession has fixed constants D Q S T, not functions of (a,b,c).
Therefore S2921HeightLeProcessionPointwise does not specialize to
S2920HeightLeProcession: one first needs uniform global bounds

  S2921Q a b c <= Qconst,  S2921S a b c <= Sconst,  S2921T a b c <= Tconst

for all ABC triples (or a chosen collection with fixed data), together with the
height-to-collection identification.

Even then, the J-height and the collection bound live in different objects:
Height.logHeight₁ (abcJInvariant a b c) is analytic, while collectionBound is a
linear combination of D/Q/S/T.  No theorem in the tree identifies them.

The missing object is exactly this identification plus the uniform bounds; the
definitions S2921D/S2921Q/S2921S/S2921T are real candidates, not a proof.
-/

#check S2921D
#check S2921Q
#check S2921S
#check S2921T
#check S2921Q_eq_regionVolume
#check S2921D_nonneg
#check S2921HeightLeProcessionPointwise
#check S2920HeightLeProcession
#print axioms S2921Q_eq_regionVolume
#print axioms S2921D_nonneg

end LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
end
