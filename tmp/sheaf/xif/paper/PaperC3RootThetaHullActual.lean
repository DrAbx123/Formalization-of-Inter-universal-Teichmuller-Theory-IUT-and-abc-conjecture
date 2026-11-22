import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.PaperC3PrimitiveMu2lRootActual

-- Root-valued paper theta: q_v = q^(1/2l), theta_j = q_v^(j^2);
-- its actual mu_{2l} orbit/hull and the exact q-parameter comparison.
-- The q-parameter power q^(j^2) is NOT used as paper theta; it is only the
-- 2l-th power comparison target.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3PrimitiveMu2lRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- Root-valued paper theta point.
noncomputable def paperRootThetaHullPoint
    (j : SignedLabel l.value) : RootThetaCarrier (G := G) :=
  paperRootThetaImagePoint (G := G) j

-- Independent mu_{2l} action on the root theta point.
theorem primitiveMu2lRoot_zeta_ne_zero (v : V) :
    (primitiveMu2lRoot (G := G) v).zeta ≠ 0 := by
  intro h
  have hp := (primitiveMu2lRoot (G := G) v).zeta_pow
  rw [h] at hp
  have hpos : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  rw [zero_pow hpos] at hp
  exact zero_ne_one hp

noncomputable def paperRootThetaMuPoint
    (m : Nat) (j : SignedLabel l.value) : RootThetaCarrier (G := G) :=
  fun v => (Units.mk0 ((primitiveMu2lRoot (G := G) v).zeta ^ m)
    (pow_ne_zero m (primitiveMu2lRoot_zeta_ne_zero (G := G) v))) *
    paperRootThetaUnit (G := G) j v

noncomputable def paperRootThetaMuOrbit
    (j : ThetaLabel (l := l)) :
    Set (RootThetaCarrier (G := G)) :=
  Set.range (fun m : Nat => paperRootThetaMuPoint (G := G) m
    (thetaLabelToSigned (l := l) j))

-- Actual root-valued theta hull: union of the mu_{2l} orbits.
noncomputable def paperRootThetaHull :
    Set (RootThetaCarrier (G := G)) :=
  Set.iUnion (fun j : ThetaLabel (l := l) => paperRootThetaMuOrbit (G := G) j)

theorem paperRootThetaHull_mem
    (j : ThetaLabel (l := l)) (m : Nat) :
    paperRootThetaMuPoint (G := G) m (thetaLabelToSigned (l := l) j) ∈
      paperRootThetaHull (G := G) :=
  Set.mem_iUnion.mpr ⟨j, ⟨m, rfl⟩⟩

-- The q-parameter power comparison target q^(j^2), not paper theta.
noncomputable def paperQParameterThetaPoint
    (j : SignedLabel l.value) :
    (v : V) → CommonPrimeCompletion (G.place v) :=
  fun v => (G.qUnit v : CommonPrimeCompletion (G.place v)) ^
    ((gaussExponent j.1).toNat)

-- Exact log-volume/comparison API still needed for the root hull.
structure RootThetaHullLogComparison where
  rootHullLogVolume : ENNReal
  qParameterLogVolume : ENNReal
  comparison : rootHullLogVolume <= qParameterLogVolume

def RootThetaHullLogComparisonRequired : Prop :=
  Nonempty (RootThetaHullLogComparison)

#check paperRootThetaHullPoint
#check paperRootThetaMuPoint
#check paperRootThetaMuOrbit
#check paperRootThetaHull
#check paperRootThetaHull_mem
#check paperQParameterThetaPoint
#check RootThetaHullLogComparison

end LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual

end