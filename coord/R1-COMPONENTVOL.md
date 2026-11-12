# R1 — componentVol normalization check (A876/A878)

Status: source-level read of lana tree. No olean is currently built for these lana files,
so this is a **statement-level** normalization audit, not a compiled proof claim.

## 1. Definitions (exact source)

### Tensor packet
- file Iut/Concrete/LocalConstruct/Packet.lean:520-521:
  Tensor K vQ c := tensor product over baseField vQ of Factor' K vQ (c j).
- baseField at Packet.lean:472-474:
  baseField (.finite p) = Q_p, baseField .infinite = R.
- PacketIndex at Packet.lean:535:
  PacketIndex vQ c = forall j, Fin (finrank (baseField vQ) (Factor' K vQ (c j))).
- finrank_tensor_eq_card (Volume.lean:219-221):
  finrank (baseField vQ) (Tensor K vQ c) = Fintype.card (PacketIndex vQ c)
  = product_j [K_{c j} : baseField vQ].

So the normalization denominator is the **product of local degrees**, not a sum.

### Normalized Haar log-volume
Volume.lean:193-198:

    noncomputable def componentVol (S : Set (Tensor K vQ c)) : Real :=
      Real.log ((haar vQ c S).toReal / (haar vQ c (integralAt vQ c)).toReal) /
        Module.finrank (baseField vQ) (Tensor K vQ c)

Thus:
    componentVol(S) = log(mu(S)/mu(I)) / [Tensor : baseField],
    componentVol(integral) = 0.

### Nonarchimedean scaling theorem
ScaleVolume.lean:116-122:

    theorem componentVol_prod_incl_smul_integral
      (hc : forall j, IsOver K p (c j))
      (w : iota -> FinitePlace K) (h : forall j, c j = Place.finite (w j))
      (y : forall j, completionAt K (w j)) (hy : forall j, y j != 0) :
      componentVol (.finite p) c
        ((prod j, incl p c j (w j) (h j) (y j)) • integral p c)
      = -(sum j, ordp K (w j) (y j)) * Real.log p

This is the exact internal theorem corresponding to §12.1 L3.

### Archimedean scaling theorem
Volume.lean:249-263:

    theorem componentVol_arch_scale (t : Real) (ht : 0 < t) :
      componentVol .infinite c (algebraMap R (Tensor K .infinite c) t • integralAt .infinite c)
      = Real.log t

So a radial archimedean scale t contributes log t, with no 1/2 or factor of local degree.

## 2. Normalization conclusion for L3

Let a capsule j have j+1 tensor factors, and let
hull = p^{-sum_i h_i} · M with M the maximal order. Multiplication of all coordinates by
p^{-sum h_i} scales the Haar measure by
    (p^{-sum h_i})^{[Tensor : Q_p]}.
Dividing by the finrank (the same [Tensor : Q_p]) gives exactly

    componentVol(hull) = (sum_i h_i) · log p.

This is independent of the individual local degrees and of the number of factors; it is
the content of componentVol_prod_incl_smul_integral with y_j = p^{-h_j} (or a product of
local units whose ord sums to sum h_i). Therefore:
- L3 formula mu(hull) = sum_i h_{w_i} log p is **matched exactly** by lana componentVol;
- **no (j/2)d correction is needed** for the lana definition;
- the product finrank is the normalization denominator, but it cancels in the hull ratio
  because the ratio is a pure scalar scaling of the integral model.

Archimedean case: componentVol_arch_scale gives log t; if the metric scaling is t on each
real/complex factor, the tensor dimension factor also cancels. No d/2 appears.

## 3. Effect on L5 / V

L5 in ROUTES-FINAL-GAP §12.1:
    V = ((l+5)/4) · D_exact,
    D_exact = sum_w weight(w) · h_w · log p_w + archimedean terms.

Since componentVol already returns sum h_w log p at a prime and log t at infinity, the
constant in L5 is unchanged: there is no additional (j/2)d from componentVol. The only
possible extra factors in L5 are the procession weights (tupleWeight, weight_sum_one) and
the division by the number of capsules in processionVol; those are separate from R1 and
are not componentVol normalization factors.

Verdict for R1: **normalization matches L3; no correction**. This is source-read only
(the lana files have no olean at the time of this report), so it is a statement-level
conclusion, not a green theorem.
