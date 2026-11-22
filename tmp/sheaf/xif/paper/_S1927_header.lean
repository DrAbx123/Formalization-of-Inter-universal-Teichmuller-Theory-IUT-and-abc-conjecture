/-!
# S1927: the global realified Frobenioid C⊩mod and the global log-shell

Layer: **O** (original Theta-link / q-pilot), on the source-faithful
`S1895PaperO` of `S1895OIdentificationsActual`.

## What this file constructs

1. **The global realified Frobenioid C⊩mod.**  IUT I, Example 3.5, (i), writes
   C⊩mod for the realification of the Frobenioid of [FrdI], Example 6.3,
   associated to the number field Fmod with trivial Galois extension.  Its
   divisor monoid ΦC⊩mod is the realification of the effective arithmetic
   divisor monoid; the realification replaces Z≥0 by R≥0 (Frobenioids I,
   Proposition 5.3 and the effect table of the introduction).  The file
   constructs the actual realified effective divisor cone

     (HeightOneSpectrum O_Fmod →₀ R≥0) × (InfinitePlace Fmod → R≥0),

   proves it is a sharp, integral, saturated divisorial monoid, identifies its
   Grothendieck group with the explicit real divisor group

     (HeightOneSpectrum O_Fmod →₀ R) × (InfinitePlace Fmod → R),

   and builds the model Frobenioid presentation of Theorem 5.2 from the actual
   principal divisor map.  The result is a genuine `Iut.FrobenioidPresentation`
   on the one-object/one-arrow base category, not a carrier record and not a
   gate witness.  It is attached to the base field Fmod of the S1895 input by
   `paperGlobalRealifiedFrobenioid`.

2. **The q_v zero-locus divisor.**  For every bad place of the S1895 input, the
   actual base Fmod prime divisor `b.1.maximalIdeal` is put in the realified
   divisor monoid with coefficient one; the global divisor is the finite sum
   over the actual bad places.  This is the literal zero-locus prime divisor
   (support) of the q_v; the q_v valuation order is carried by the actual
   S1487 q-candidate and is not replaced by a fabricated coefficient.

3. **The finite global log-shell/tensor packet.**  At every finite prime place
   of the S1895 one-column, the actual completed local field, its units and the
   actual norm-log degree give a `SourceLogShellDatum`; the direct-sum packet
   `IQ(sum_v I_v)` and the tensor-packet decomposition are then the actual
   finite global log-shell packet over the one-column index.

## Exact first missing

The finite log-shell packet is constructed, but the **archimedean log-shell
datum at the archimedean places of Fmod** is not: `SourceLogShellDatum` is
nonarchimedean (it carries a prime p and the (p*_v)^{-1}-scaled pre-log-shell),
while IUT III, Definition 1.1, (ii), gives a distinct closed-interval/orbit
log-shell at the archimedean places.  The type `S1927FirstMissing` records the
exact missing datum.  The second gap is the actual four coric vertices
(env/gau/LGP/lgp) and the Kummer evaluation square on them, recorded in
`SourceKummerEvaluationArrows` R3; the reduced square is parameterized by its
four strips precisely because the paper vertices are not constructed.  The
full log-Kummer package on 1,circU_Q is `S1927FullLogKummerUQ`; it is
assembled from the constructed finite data and the two named missing inputs.
No Frobenioid, log-shell, Kummer arrow or evaluation square is fabricated.

## Source locations

* IUT I, Example 3.5, (i) (global realified Frobenioids); [FrdI], Example 6.3
  and Theorem 6.4; [FrdI], Proposition 5.3 (realification).
* IUT III, Definition 3.8, (i) (q-pilot object determined by the q_v);
  IUT III, Theorem 3.11, (ii), (iii), (a), (b) (log-Kummer and evaluation
  square); Definition 1.1, (i), (ii) (log-shells).
* The reduced source interface is `SourceKummerEvaluationArrows` (R3: the
  env/gau/LGP/lgp vertices are not constructed; R6: the q-pilot anchor
  identification is not made).

## Verification

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  The missing types are definitions, not inhabited.
-/

import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import LeanFormal.IUT.Foundations.Arithmetic.NormLog
import Mathlib.Data.NNReal.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual

namespace Realified

open CategoryTheory IsDedekindDomain NumberField
open scoped BigOperators

