# ACTUAL-FINALL-DATA-PLAN — ArithmeticTensorTupleBlock, RootExtension/FinalL, transport lemmas

Status: READ-ONLY analysis, 2026-11-12. No compile.
Question: identify ArithmeticTensorTupleBlock; identify RootExtension/FinalL finite
extension and FiniteDimensional data; list the transport lemmas needed for the
actual FinalL-valued carrier.

## 1. ArithmeticTensorTupleBlock

Definition (FinitePlaceArithmeticTensorBlocks.lean:26-27):
  abbrev ArithmeticTensorTupleBlock (tuple : (i : ι) → V i) :=
    FinitePadicTensor (p := p)
      (fun i => CommonPrimeCompletion (places i (tuple i))).

So it is a finite tensor product of the actual local-field completions at the
tuple of places, not a finite product ring and not an abstract model. Base field
is ℚ_[p]. Existing instances/facts:
- finitePadicTensorFinite: FiniteDimensional ℚ_[p] (FinitePadicTensor ...)
  for Finite ι (FinitePadicTensorTopology.lean:37-40);
- finrank_arithmeticTensorTupleBlock:
    finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
      = ∏ i, finrank ℚ_[p] (CommonPrimeCompletion (places i (tuple i)))
  (FinitePlaceArithmeticTensorBlocks.lean:97-100);
- finrank_arithmeticTensorTupleBlock_pos for Finite ι (same file:103-107);
- arithmeticTensorBlocksAlgEquiv:
    ArithmeticPacketTensor places ≃ₐ[ℚ_[p]]
      ((tuple : (i : ι) → V i) → ArithmeticTensorTupleBlock places tuple)
  (same file:29-32);
- arithmeticTensorTupleProjection and its tprod/log-region transport
  (same file:46-94);
- finitePadicTensorCoordinates:
    FinitePadicTensor ≃ₗ[ℚ_[p]]
      (FinitePadicTensorIndex → ℚ_[p])
  where FinitePadicTensorIndex = (i : ι) → Fin (finrank ℚ_[p] (M i))
  (FinitePadicTensorTopology.lean:42-50).

Is there a direct equivalence to Fin d → ℚ_[p]? Not at this name. The existing
coordinates target is the dependent product FinitePadicTensorIndex. A direct
Fin d → ℚ_[p] continuous linear equivalence is obtained from any finite basis
via Module.finBasis, exactly as in FinitePadicHaarScaling.lean:28-29:
  let e : M ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] M) → ℚ_[p]) :=
    (Module.finBasis ℚ_[p] M).equivFun.toContinuousLinearEquiv.
The missing transport is only the specialization/definition for
ArithmeticTensorTupleBlock; the ingredients already exist.

## 2. RootExtension and FinalL

RootExtension (PaperC3ThetaRootActual.lean:35-36):
  abbrev RootExtension (v : V) : Type u :=
    AlgebraicClosure (CommonPrimeCompletion (G.place v)).
So RootExtension is an algebraic closure, not a finite extension of the
completion. It has no FiniteDimensional instance over CommonPrimeCompletion;
the algebraic closure is generally infinite-dimensional.

FinalL (PaperFinalLValuedTensorCarrierActual.lean:42-43):
  abbrev FinalL (T) (b) : Type :=
    RootExtension (G := finalLGeometry T b) PUnit.unit.
Thus FinalL is also an algebraic closure (over the qVFamily completion), not a
finite extension. FinalLValuedCarrier (same file:45-46):
  abbrev FinalLValuedCarrier : Type :=
    TensorProduct ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) (FinalL T b).
It is a tensor product of the finite qVFam block over ℚ_p with the algebraic
closure FinalL.

Finite-dimensional facts that do exist:
- qVFamTensorBlock T b is a FinitePadicTensor of completions, hence
  FiniteDimensional ℚ_[qVFamTensorP T b]; this follows from the general
  FinitePadicTensor instances.
- LZeta (PaperFinalLMu2lExtensionActual.lean) is an IntermediateField
  (FinalL T b) (FinalL T b). PaperLZetaNormedActual.lean:57-74 proves
  lZetaField_eq_top : LZetaField T b = ⊤, then lZetaEquivFinalL and
  lZetaFiniteDimensional : FiniteDimensional (FinalL) (LZeta).
  This FiniteDimensional instance is trivial: LZeta = FinalL (rank one). It is
  NOT a genuine finite 2l-Kummer extension of FinalL; the 2l-th root is already
  in the algebraic closure.

FinalLValuedCarrier finite-dimensionality is NOT proved:
- S1002FiniteQuotientLinearizationActual.lean:50-52 defines
    S1002PaperPacketFiniteDimensional : Prop :=
      FiniteDimensional ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b).
  It is an explicit Prop target, no instance.
- S965FinalLCarrierTopologyActual.lean:37-50 defines
    S965CarrierLinearization with d : Nat and
    e : FinalLValuedCarrier T b ≃ₗ[ℚ_p] (Fin d → ℚ_p),
  and linearizationOfFinite only from [Module.Finite] and [Module.Free].
  S965CarrierLinearizationRequired is therefore a named GAP, not a theorem.

Important: one cannot prove FiniteDimensional ℚ_p (FinalLValuedCarrier T b)
from FinalL being algebraic; the Q_p-dimension of the algebraic closure is
infinite. A genuine finite-dimensional reduction must either:
  (a) work with the finite qVFam block and its tensor scalar extension over
      FinalL, where rank over FinalL is finite, but Q_p-dimension is infinite;
  (b) replace the full packet by the finite log-shell quotient
      (S1002FiniteQuotientBridgeExact), which is the named finite carrier;
  (c) impose finite-dimensionality as explicit data (S965/S1002 Props).

## 3. Transport lemma list

### A. ArithmeticTensorTupleBlock -> finite coordinates
A1. ArithmeticTensorTupleBlock_finiteDimensional:
    FiniteDimensional ℚ_[p] (ArithmeticTensorTupleBlock places tuple).
    Existing: finitePadicTensorFinite + abbrev unfolding; likely rfl/inferInstance.
A2. ArithmeticTensorTupleBlock_finrank:
    finrank = ∏ i, finrank ℚ_[p] (CommonPrimeCompletion ...). Existing
    finrank_arithmeticTensorTupleBlock.
A3. ArithmeticTensorTupleBlock_coordinates:
    ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      (FinitePadicTensorIndex ... → ℚ_[p]).
    Existing finitePadicTensorCoordinates after unfolding; record as a
    specialization lemma.
A4. ArithmeticTensorTupleBlock_continuousLinearEquiv_Fin:
    ArithmeticTensorTupleBlock places tuple ≃L[ℚ_[p]]
      (Fin (finrank ...) → ℚ_[p]).
    New but immediate from Module.finBasis (same pattern as
    FinitePadicHaarScaling). This is the exact form for Haar/measure transport.
A5. ArithmeticTensorTupleBlock_finrank_pos: existing.

### B. qVFamTensorBlock / FinalL-valued carrier
B1. qVFamTensorBlock_finiteDimensional:
    FiniteDimensional ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b).
    Should follow from qVFamTensorBlock being ArithmeticTensorTupleBlock at Unit.
    Check the abbrev unfolding; if the instance is not found by inference,
    add an explicit instance theorem.
B2. qVFamTensorBlock_finrank:
    finrank = finrank of CommonPrimeCompletion at the qVFam place (one factor).
B3. FinalLValuedCarrier_rank_over_FinalL:
    Module.finrank (FinalL T b) (FinalLValuedCarrier T b) =
      Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b).
    New. This is the honest finite-rank statement over FinalL (not over Q_p).
B4. FinalLValuedCarrier_finiteDimensional_over_FinalL:
    FiniteDimensional (FinalL T b) (FinalLValuedCarrier T b).
    New; follows from B1 and TensorProduct finite rank if the scalar tower and
    free module data are supplied.
B5. FinalLValuedCarrier_tensorBasis:
    a FinalL-basis of FinalLValuedCarrier from a Q_p-basis of qVFamTensorBlock.
    New; TensorProduct basis transport.
B6. FinalLValuedCarrier_linearization_of_finiteFree:
    [Module.Finite] [Module.Free] -> S965CarrierLinearization. Existing
    linearizationOfFinite (S965FinalLCarrierTopologyActual).

### C. RootExtension / FinalL field transport
C1. RootExtension_def_eq: RootExtension = AlgebraicClosure (completion). rfl.
C2. RootExtension_ringEquiv_source: existing
    rootExtensionEquivRingEquiv / rootExtensionEquivUnits
    (PaperRootExtensionEquivActual.lean:39-58).
C3. RootExtension_norm_transport: existing rootExtensionNorm and its
    twoLthRoot/paperRootThetaUnit compatibility.
C4. FinalL_is_rootExtension: rfl (abbrev).
C5. FinalL_not_finiteDimensional:
    no FiniteDimensional ℚ_[p] (FinalL T b).
    This is an obstruction theorem, not a transport lemma; it should be
    recorded so nobody tries to prove finite-dimensionality of FinalL over Q_p.
C6. LZeta_eq_top: existing lZetaField_eq_top, with
    lZetaFiniteDimensional (trivial rank-one consequence).

### D. Finite quotient / replacement route
D1. FiniteQuotientBridge_of_finiteDimensional: existing
    S1002FiniteQuotientLinearizationActual:36-41.
D2. finiteCarrier_selfLinearization: existing (same file:44-48).
D3. S1002FiniteQuotientBridgeExact:
    S1002PaperPacketFiniteDimensional OR FiniteQuotientBridge of the carrier.
    This is the exact disjunction that replaces the missing Q_p-finiteness.
D4. S965CarrierTopologyAndLinearizationRequired:
    linearization + carrier topology; exact nonzero target.

## 4. What can be proved now vs what is new

Can be proved now (ingredients exist):
- ArithmeticTensorTupleBlock_finiteDimensional;
- ArithmeticTensorTupleBlock_finrank (already named);
- ArithmeticTensorTupleBlock_coordinates via finitePadicTensorCoordinates;
- ArithmeticTensorTupleBlock_continuousLinearEquiv_Fin via Module.finBasis;
- qVFamTensorBlock_finiteDimensional/finrank (after unfolding);
- RootExtension ring/norm equivalences (already existing).

New substantive transport:
- FinalLValuedCarrier_rank_over_FinalL (B3);
- FinalLValuedCarrier_finiteDimensional_over_FinalL (B4);
- FinalLValuedCarrier_tensorBasis (B5);
- the exact finite quotient bridge or the S965 linearization data if one wants
  the Q_p-coordinate form.

Not provable / do not assume:
- FiniteDimensional ℚ_[p] (FinalL T b); FinalL is an algebraic closure.
- FiniteDimensional ℚ_[p] (FinalLValuedCarrier T b) without additional
  finite-free data; this is exactly S1002PaperPacketFiniteDimensional, a Prop.
- LZeta as a nontrivial finite 2l-Kummer extension; lZetaField_eq_top makes it
  rank one and therefore does not supply the missing 2l-root.

## 5. Recommended plan

1. Prove the immediate specializations A1-A5 for ArithmeticTensorTupleBlock;
   use Module.finBasis for the continuous linear equiv to Fin d -> ℚ_[p].
2. Prove B1-B2 for qVFamTensorBlock by unfolding the qVFam place tuple.
3. Prove B3-B5 over FinalL: tensor a Q_p-basis of the finite block with 1 in
   FinalL; this is the honest finite-rank statement. Do not claim Q_p-finite.
4. For any consumer that needs Fin d -> ℚ_[p] topology/Haar, use either:
   - the finite quotient carrier S1002FiniteQuotientBridgeExact, or
   - S965CarrierLinearization with explicit Module.Finite/Free data.
5. Record C5 and the LZeta top equality as obstructions, so the missing 2l-root
   is not mistaken for a trivial finite extension.

No Lean file written; no compile claimed.