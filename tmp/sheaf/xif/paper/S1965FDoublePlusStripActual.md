# S1965: F-double-plus-prime-strip carrier and actual C-mod packaging

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S1965FDoublePlusStripActual.lean.

## Outcome

**EXIT=0**.  The F^double-plus-prime-strip carrier type is defined and an
actual instance is constructed for the C^double-plus-mod global realified
Frobenioid.  The actual C^double-plus-env / C^double-plus-gau packaging is
**missing**; the exact first missing is the local theta/Gaussian monoid
assignment of IUT II, Corollary 4.6, (iv), and Proposition 4.1.  A conditional
packaging from any realified local monoid family is constructed.  No fake
type/Prop slot, empty type, arbitrary inhabitant, sorry or axiom is used.

## Constructed (checked)

* LeanFormal.IUT.FDoublePlusPrimeStrip V: the carrier data
  (C^double-plus, Prime(C^double-plus) ~= V, F^dagger, {rho_v}) of IUT I,
  Definition 5.2, (iv), and IUT II, Definition 4.9, (vii)--(viii):
  - global : Iut.FrobenioidPresentation (C^double-plus);
  - basePoint, primeIndex, primeEquiv : primeIndex ~= V;
  - localDivisor v : the actual Phi(C^double-plus,v) as an AddSubmonoid of
    the global divisor monoid, with localDivisorEquiv v : localDivisor v ~= NNReal;
  - fDagger : FPrimeStrip V (F^dagger);
  - localRealified v with localRealifiedEquiv v : localRealified v ~= Multiplicative NNReal;
  - rho v : Multiplicative (localDivisor v) ~= localRealified v.
* paperModFDoublePlus D: an actual inhabitant over NumberFieldPlace (PaperFmod D), with
  - global := paperGlobalRealifiedFrobenioid D (the actual S1927 C^double-plus-mod);
  - the actual v-supported components of the realified effective divisor monoid,
    with explicit finite/infinite place equivalences to NNReal;
  - fDagger := numberFieldPrimeStrip reindexed to NumberFieldPlace;
  - localRealified := Multiplicative NNReal;
  - rho := the place-component equivalence, sending the prime generator to 1.
* paperCoricDoublePlusOfLocalMonoids D M e: the conditional env/gau packaging
  from a local monoid family M with e : M v ~= R_{>=0} (the realified local
  theta/Gaussian monoid data of Corollary 4.6, (v)).
* paperOneColumnDoublePlus D e: the conditional reindexing to the S1959
  one-column index FinitePrimePlace 2 7 from a place equivalence e.

## Exact first missing

The local theta monoid assignment PsiFenv(daggerHT_Theta) (and PsiFgau) of
IUT II, Corollary 4.6, (iv), built by the group-theoretic algorithm of
IUT II, Proposition 4.1, (i)--(iv).  The active LeanFormal/Iut tree has no
theta monoid, no Gaussian monoid, and no categorical local split Frobenioid
C^dagger_v.  Consequently the local realified monoid families for env/gau and
the actual C^double-plus-env/C^double-plus-gau are not constructed.  No
ThetaMonoid type, Prop slot or Nonempty gate is introduced.

A second, independent missing component is the geometric F^dagger part: the
tempered/etale fundamental group of the once-punctured elliptic curve.
numberFieldPrimeStrip has trivial geometric kernels.

The S1959 reduced vertices use FinitePrimePlace 2 7, while the actual
C^double-plus-mod prime set is NumberFieldPlace Fmod; no place equivalence is
constructed, so the reduced vertices are not silently identified with the
C-mod carrier.

## Verification

* source SHA256: BF6876670EBDE3438E80E145C794F6A1E4E63FF0B98D41E313404656E411B4B4
* EXIT=0: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1965FDoublePlusStripActual.olean tmp/sheaf/xif/paper/S1965FDoublePlusStripActual.lean
* olean: 636168 bytes, SHA256 FE664C23DF6B7AB750F984E62303EEFA28DDEDE045E44682540CE8179BC75785
* axioms: propext, Classical.choice, Quot.sound only; no sorryAx
* consumer: tmp/sheaf/xif/paper/_S1965Consumer.lean, EXIT=0

## Not run

Full Project build, target comparator, independent review.
