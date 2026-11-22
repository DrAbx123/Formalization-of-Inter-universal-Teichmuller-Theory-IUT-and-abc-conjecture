/- Route 7.2/7.3 wiring documentation for the G-K lane.

## What the universal local field provides

* Mzk1G1UniversalLocalFieldExistsFinalActual.universalLocalFieldExists_final (d)
    (h : ∃ N, ResidueRootGeneration d N) : UniversalLocalFieldExists (p := p) d

  Unfolding UniversalLocalFieldExists (in LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual):
  it gives L : Type, Field L, Algebra (Padic p) L, FiniteDimensional (Padic p) L,
  Normal (Padic p) L, and ContainsBoundedExtensions p d L, i.e. every degree <= d
  extension of Q_p embeds into L.

## How it feeds GKCompactInput

GKCompactInput (Mzk1G1DisjointFamilyActual) records X, top, comp, non, delta,
delta_cont, delta_cover.  Its X is the product over v in V of Y_n(L_v)^d with the actual
local fields L_v = universal local field at p = v.  The G-K lane therefore needs, for each
p in V_non, the L_v and ContainsBoundedExtensions output above; the compactness/topology
of X is a separate analytic input of route 7.3 and is not produced by this file.

## Different bound constants

* localDifferentOrder_lt_logShell_mul
    (Mzk1G1UniversalSerreDeltaBoundActual): delta < e * (v_p(e) + 2).
* With e <= d this yields delta <= d * (v_p(d) + 2) =: B.
* Separation constant: p ^ (-(B : Z)) (Mzk1G1UniversalSeparationConstantActual,
  differentBound; the Serre version uses the +2 constant).
* The residue-root assembly (Mzk1G1UniversalResidueRootGenerationActual) is the only
  remaining step; it consumes SeparationInput with this B.
-/
import tmp.sheaf.xif.paper.Mzk1G1UniversalLocalFieldExistsFinalActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalContainsBoundedActual
import tmp.sheaf.xif.paper.Mzk1G1DisjointFamilyActual
