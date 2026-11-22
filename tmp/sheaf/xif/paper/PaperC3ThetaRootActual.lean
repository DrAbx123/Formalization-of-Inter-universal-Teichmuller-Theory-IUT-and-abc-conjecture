import tmp.sheaf.xif.paper.PaperSourceGeometryActual
import tmp.sheaf.n8.closure.C3Roots

-- Correct 2l-th root Theta units on the completion-valued geometry
--
-- Paper: q_v := q^(1/2l), theta_v(j) := q_v^(j^2) = q^(j^2/(2l)).
-- The completion generally has no 2l-th root.  We construct the actual root in
-- the algebraic closure (the Kummer extension), via C3Roots.algClosedRootSystem,
-- and place the resulting Theta units in the product of the algebraic closures.
-- The old completion qUnit^(j^2) is not used as the paper theta value.
-- The tensor-packet lift of these extension units is recorded as an exact gap.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- The algebraic-closure Kummer extension at each source place.
abbrev RootExtension (v : V) : Type u :=
  AlgebraicClosure (CommonPrimeCompletion (G.place v))

-- Actual algebraic-closure product carrier for the root Theta units.
abbrev RootThetaCarrier : Type (max u v) :=
  (v : V) → (RootExtension (G := G) v)ˣ

-- Actual 2l-th root system of the actual q unit at each place.
noncomputable def rootSystemAt (v : V) :
    NatRootSystem (unitToAlgClosed (G.qUnit v)) :=
  algClosedRootSystem (G.qUnit v)

-- Actual 2l-th root q_v of the q unit in the algebraic closure.
noncomputable def twoLthRootAt (v : V) :
    (RootExtension (G := G) v)ˣ :=
  (rootSystemAt (G := G) v).root (2 * l.value)

theorem twoLthRootAt_pow (v : V) :
    twoLthRootAt (G := G) v ^ (2 * l.value) =
      unitToAlgClosed (G.qUnit v) := by
  unfold twoLthRootAt rootSystemAt
  exact NatRootSystem.pow_self (algClosedRootSystem (G.qUnit v))
    (2 * l.value) (by
      exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)

-- Correct paper Theta unit q_v^(j^2), in the algebraic closure.
noncomputable def paperRootThetaUnit
    (j : SignedLabel l.value) (v : V) :
    (RootExtension (G := G) v)ˣ :=
  twoLthRootAt (G := G) v ^ (gaussExponent j.1).toNat

theorem paperRootThetaUnit_pow_twoL
    (j : SignedLabel l.value) (v : V) :
    paperRootThetaUnit (G := G) j v ^ (2 * l.value) =
      (unitToAlgClosed (G.qUnit v)) ^ (gaussExponent j.1).toNat := by
  unfold paperRootThetaUnit
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [twoLthRootAt_pow]

-- Correct root Theta image point in the root extension carrier.
noncomputable def paperRootThetaImagePoint
    (j : SignedLabel l.value) : RootThetaCarrier (G := G) :=
  fun v => paperRootThetaUnit (G := G) j v


/-- Paper theta labels: positive representatives j = 1,...,l* of the ±-pair,
removing the SignedLabel two-to-one duplication. -/
abbrev ThetaLabel : Type := { j : SignedLabel l.value // 0 < j.1 }

/-- Map a positive paper theta label to its SignedLabel representative. -/
def thetaLabelToSigned (j : ThetaLabel (l := l)) : SignedLabel l.value := j.1

/-- The paper label map is injective. -/
theorem thetaLabelToSigned_injective :
    Function.Injective (thetaLabelToSigned (l := l)) := by
  intro a b h
  exact Subtype.ext h


/-- The Gaussian exponent of a positive paper ThetaLabel is at least one. -/
theorem thetaLabel_gaussExponent_one_le (j : ThetaLabel (l := l)) :
    1 ≤ (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat := by
  unfold gaussExponent thetaLabelToSigned
  have hpos : (0 : ℤ) < (j.1).1 := j.2
  have hsq : (1 : ℤ) ≤ (j.1).1 ^ 2 := by nlinarith
  have hz0 : (0 : ℤ) ≤ (j.1).1 ^ 2 :=
    le_of_lt (lt_of_lt_of_le zero_lt_one hsq)
  have hcast : (((j.1).1 ^ 2).toNat : ℤ) = (j.1).1 ^ 2 :=
    Int.toNat_of_nonneg hz0
  have h : (1 : ℤ) ≤ (((j.1).1 ^ 2).toNat : ℤ) := by
    simpa [hcast] using hsq
  exact_mod_cast h

/-- Root Theta image point indexed by a positive paper label. -/
noncomputable def paperRootThetaImagePointTheta
    (j : ThetaLabel (l := l)) : RootThetaCarrier (G := G) :=
  paperRootThetaImagePoint (G := G) (thetaLabelToSigned (l := l) j)

/-- Root Theta image set over positive paper labels only. -/
noncomputable def paperRootThetaImageSetTheta :
    Set (RootThetaCarrier (G := G)) :=
  Set.range (paperRootThetaImagePointTheta (G := G))

theorem paperRootThetaImagePointTheta_mem
    (j : ThetaLabel (l := l)) :
    paperRootThetaImagePointTheta (G := G) j ∈
      paperRootThetaImageSetTheta (G := G) :=
  ⟨j, rfl⟩

/-- Backwards-compatible name: the root Theta image set is the positive-label
ThetaLabel image set, not the full SignedLabel range. -/
noncomputable abbrev paperRootThetaImageSet : Set (RootThetaCarrier (G := G)) :=
  paperRootThetaImageSetTheta (G := G)

/-- Backwards-compatible membership theorem on positive labels. -/
theorem paperRootThetaImagePoint_mem (j : ThetaLabel (l := l)) :
    paperRootThetaImagePoint (G := G) (thetaLabelToSigned (l := l) j) ∈
      paperRootThetaImageSet (G := G) :=
  paperRootThetaImagePointTheta_mem (G := G) j




-- Exact gap: lifting the extension-valued root Theta units to the actual
-- tensor-packet/arithmetic-tuple carrier is not constructed here. The
-- algebraic-closure product carrier is actual; the tensor lift is the missing
-- object, not replaced by a completion qUnit^(j^2) value.
structure RootThetaTensorPacketGap where
  tensorCarrier : Type
  imageSet : Set tensorCarrier
  unitMap : RootThetaCarrier (G := G) → tensorCarrier
  unitMap_compat : Prop

def RootThetaTensorPacketGapRequired : Prop :=
  Nonempty (RootThetaTensorPacketGap (G := G))

#check RootExtension
#check RootThetaCarrier
#check twoLthRootAt
#check twoLthRootAt_pow
#check paperRootThetaUnit
#check paperRootThetaUnit_pow_twoL
#check paperRootThetaImagePoint
#check paperRootThetaImageSet
#check RootThetaTensorPacketGap

end LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

end