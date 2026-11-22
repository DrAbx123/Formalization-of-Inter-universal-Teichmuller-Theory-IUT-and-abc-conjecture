# C9 b=3 Lean bridge: R_B subset H_C and h_inf >= -S3

Task: task-365. Date: 2026-10-25. Author: transport.
Lean BPS/Theta mining; no Lean edits; no arbitrary; no mixed/E3.
Only this file written. target_accepted=false.

## 0. Files inspected

| Lean file | lines | SHA256 |
|---|---:|---|
| LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean | 864 | 864C372A59446E77BEEB40A1925E06487A2565B8E7BE729019943C8A6A192C03 |
| LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean | 569 | 8FB1AB1651E38A4628ADC5D1211C30F37375B8572522C3BFC5A56180ED1A8D59 |
| LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean | 482 | 8171F4C6F3BBE3D08E4D5119238222D57FF519DB68FDB5BFD9B600646512A355 |
| LeanFormal/IUT/IUTII/Frobenioid/Example36ArchimedeanLocal.lean | 653 | 6C4331597E04F9D80FA8B57379E23AA012B8026890E5CD264868EEDE5765D185 |

Additional modules read at header level:

- LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean;
- LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullSharpUpperBound.lean;
- LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTupleHullVolume.lean.

## 1. Verdict

The b=3 P6 hypotheses

    (H_R)  R_B subset H_C,
    (H_arch)  h_inf >= -S3 = -(12/41) log 12301

are NOT formalized and NOT derivable from the current Lean declarations.

The Lean development has:

- a generic value-monoid possible-image union and holomorphic hull;
- finite-place possible-image sets for the Step (v) linear action;
- generic finite-arithmetic hull log-volume and upper bound interfaces;
- BPS/F-turnstile-times-mu-prime-strip poly-isomorphism carriers;
- a local archimedean ball dictionary.

It does NOT have:

- a declaration of the b=3 principal q value or the constant S3;
- a declaration of the B=O_K/B=I branch region R_B;
- a declaration of the target hull H_C for the complete b=3 target;
- a declaration of the global archimedean hull volume h_inf;
- any theorem R_B subset H_C or h_inf >= -S3.

Searches for the mathematical names/tokens R_B, B_I, H_A, h_inf, 12301,
12/41, and S3 in LeanFormal/IUT found no matching declarations. The only
possible-image and hull declarations are the generic ones below.

## 2. Existing possible-image declarations

### 2.1 Finite Step (v) possible images

FinitePlaceStepVAssembly.lean, line 668:

    def arithmeticTupleStepVPossibleImages
        (istar : iota) (varpi : ...) (Phi : Set (Block =~[Q_p] Block)) :
        Set Block :=
      {s | exists phi in Phi, x in arithmeticTupleCanonicalUnitReference,
           s = phi (tprod (update 1 istar varpi) * x)}

This is the set of possible images under a set Phi of linear isomorphisms. It
is a local finite Step (v) object, not the BPS/Theta target possible-image
family and not the B=O_K/B=I row region.

Proved there:

- measure_arithmeticTupleStepVPossibleImages_pos (line 678): positive Haar
  mass when Phi is nonempty;
- arithmeticTupleStepVPossibleImages_subset_endpoint (line 720): every
  possible image lies in the Step (v) endpoint container.

The endpoint inclusion is an upper container for the local Step V image, not
R_B subset H_C and not an archimedean bound.

### 2.2 Source Theta-pilot possible-image union and holomorphic hull

SourceImageHull.lean:

- PossibleThetaPilotImageAt (line 225);
- possibleThetaPilotImageSet (line 231);
- sourceHolomorphicHull (line 404);
- possibleThetaPilotImage_subset_sourceHolomorphicHull (line 408);
- sourceHolomorphicHull_paper_properties (line 447);
- sourceThetaPilotPoint_mem_sourceHolomorphicHull (line 490).

This is the closest Lean analog of the source possible-image hull. It is a
value-monoid realization of the Theta-pilot image union/hull, with the paper's
least-hull universal property. It is not the B=O_K/B=I row hull R_B:

- no B branch, O_K/I/J row, or q-volume class is defined;
- the hull lives in a value monoid, not in the IQ-level log-shell/Haar carrier;
- no target complete C or b=3 constants are present.

### 2.3 Literal arithmetic hull interface is impossible

SourceImageHull.lean, lines 530-560:

    structure LiteralArithmeticHullInterface ... where
      imageSet : Set P
      imageSet_nonempty : imageSet.Nonempty
      not_empty_isLambdaOHull : not (IsLambdaOHull Scaling empty)

    theorem literalHullInterface_impossible :
      not (Nonempty (LiteralArithmeticHullInterface P Scaling))

The proof notes that the pure hull form IsLambdaOHull contains the empty set
vacuously, so the paper's literal nondegenerate hull interface cannot be
recovered from the hull operation alone. Its missing input is the compactness
of the 1,o U_{j,vQ} together with the log-volume definition.

Therefore the Lean hull layer explicitly records that a literal H_C/volume
realization is a missing source interface, not a proved object. This blocks any
formal R_B subset H_C bridge at the current layer.

## 3. Existing hull-volume declarations

SourceImageHullVolume.lean:

- sourceLocalLogDegree (line 103);
- sourcePointVolume (line 107);
- sourceSetVolume (line 188);
- sourceHullVolume (line 193);
- sourceHullVolume_ge_imageVolume (line 209);
- sourceSetVolume_possibleImage_ge_normalized (line 247);
- SourceCompactBound (line 264);
- sourceSetVolume_possibleImage_lt_top_of_compactBound (line 273);
- sourceHullVolume_lt_top_of_hullBound (line 292);
- sourceHullVolume_ge_normalized (line 334);
- sourceHullVolume_eq_top_of_degreeFaithful (line 428);
- Audit.sourceImageHullVolume : Obligation (line 461).

What is proved: the hull volume dominates the image volume, and conditional
finiteness under the named compactness bound. What is NOT proved: the literal
IQ-level hull/Haar log-volume, compactness, and unconditional finiteness.

The audit record sourceImageHullVolume has status interface, with note:

    NOT proved: the paper's literal IQ-level hull and its Haar-log-volume,
    the compactness of the 1,o U_{j,vQ}, and unconditional finiteness;
    the abstract hull is in fact unbounded under the all-nonzero scalings.

Moreover sourceHullVolume_eq_top_of_degreeFaithful proves that under pointwise
degree faithfulness the value-realized hull volume is top. Thus the Lean hull
volume is not a finite h_C from which R_B subset H_C or h_inf >= -S3 could be
extracted.

## 4. BPS / Theta declarations

SourceFTimesMuPrimeStripPolyIsomorphism.lean provides:

- SourceFTimesMuPrimeStrip: F-prime-strip plus O-times-mu fibers, quotient
  link, descended action, realified degree;
- SourceFTimesMuPrimeStripEquivalence;
- SourceFTimesMuPrimeStripFullPolyIsomorphism;
- SourceFTimesMuPrimeStripPolyIsomorphismSquare;
- processionInclusionSquare, logThetaLatticeSquare;
- conditional SourceFTimesMuPrimeStripRem3102Diagram.

This is the BPS/F-turnstile-times-mu/poly-isomorphism carrier layer. It does
not define:

- the B=O_K/B=I possible-image row region;
- a target hull H_C;
- the finite bad possible-image family or its row exhaustion;
- any b=3 q/volume value.

The Theta modules (Foundations/Theta/OddTheta*, SourceQlTheta*, etc.) give
theta values/series/divisors, not the B-row possible-image hull or H_C.

## 5. Archimedean declarations

Example36ArchimedeanLocal.lean formalizes the local archimedean dictionary of
IUT III Example 3.6:

- RadiusRealization, localClosedBall, localPowerImage;
- the container criterion f * B(r1)^n subset B(r2) iff ||f|| r1^n <= r2;
- the log form nu(f)+n delta(r1)-delta(r2)>=0;
- normOneUnits, quotient by the norm-one circle, the log dictionary;
- instantiations for R and C.

This is a local archimedean ball/scale dictionary. It does not define:

- the global archimedean component H_C,inf of a complete C;
- the normalized global archimedean hull volume h_inf;
- any lower bound h_inf >= -S3;
- the b=3 bad-prime archimedean container or B_I subset H_C,inf.

No declaration named h_inf, ArchHull, or hInf exists in LeanFormal/IUT.

## 6. Exact missing interfaces

To formalize the two b=3 P6 hypotheses in Lean, one would need at least:

1. a b=3 source-data structure with p=12301, principal q, S3, B=O_K/B=I
   branch, and the row region R_B;
2. a target complete-C structure with BPS/Theta 0-column, possible-image
   union, target hull H_C, and the inclusion R_B subset H_C;
3. the literal IQ-level arithmetic hull carrier
   IQ(S+-_{j+1}; n,oD^vdash_{vQ}), its log-shell/O-module structure, Haar
   log-volume, and compactness of the 1,o U_{j,vQ};
4. the global archimedean component H_C,inf and a normalized h_inf with the
   inequality h_inf >= -S3.

Items 1-2 are absent; item 3 is named as the missing interface and is proved
not recoverable from the pure hull operation (literalHullInterface_impossible);
item 4 is absent from the archimedean modules.

A conditional Lean theorem of the form

    h_C >= h_B + h_inf -> h_inf >= -S3 -> h_C >= Q_p

could be written once H_R and H_arch are supplied as hypotheses, but those
hypotheses are not proved and no b=3 constants are defined. Writing such a
conditional wrapper would not close P6.

## 7. Classification

| item | Lean status |
|---|---|
| generic Step V possible images | DEFINED/PROVED |
| generic Theta-pilot value-monoid hull | DEFINED/PROVED |
| literal arithmetic hull interface | IMPOSSIBLE from hull operation |
| finite IQ-level hull/Haar log-volume | INTERFACE, NOT PROVED |
| hull volume finite | CONDITIONAL; TOP under degree faithfulness |
| BPS prime-strip/poly-isomorphism carriers | DEFINED |
| B=O_K/B=I row region R_B | NOT DEFINED |
| b=3 target H_C | NOT DEFINED |
| R_B subset H_C | NOT PROVED |
| h_inf global arch volume | NOT DEFINED |
| h_inf >= -S3 | NOT PROVED |
| b=3 P6 | NOT FORMALIZED |

## 8. Conclusion

The Lean BPS/Theta corpus supplies generic possible-image, hull, finite
arithmetic hull-volume, BPS poly-isomorphism, and local archimedean ball
layers. It does not supply the b=3 row region R_B, the target hull H_C, or the
global archimedean h_inf. The literal arithmetic hull interface is explicitly
proved impossible from the pure hull operation, and the value-realized hull
volume is top under degree faithfulness. Therefore neither b=3 P6 hypothesis
R_B subset H_C nor h_inf >= -S3 is provable from the current Lean declarations.

The exact bridge is the missing IQ-level hull/Haar/compactness interface plus
the b=3 source/target data and global archimedean hull. No Lean/Project edits
were made; no arbitrary data or mixed/E3 profile was used. target_accepted=false.
