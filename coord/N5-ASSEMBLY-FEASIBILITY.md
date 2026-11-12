# N5-ASSEMBLY-FEASIBILITY — can S3034/S3016CTheta/S3017 give N5Weak?

Status: READ-ONLY audit, 2026-11-12. No Lean file, no compile.
N5Weak means: rhs >= -A, equivalently M = A - R >= 0 with R = -rhs and
A = qPilot.absLogQ; this is the same as Corollary312Variant, not a separate
inequality.

## 1. Exact assumptions and conclusions

### S3034PacketScalarBoundActual
Context variables:
  R : S1280RemainingClauses fiveLabel
  redCompat, torCompat, orbCompat, secCompat, cusCompat : Prop with proofs
  D : SourcePilotRegionDonors (S2711I R ...)
Definitions:
  S3034Hscalar R ... D logQ a b c :=
    S3025MissingThetaUpperScalar R ... D logQ 0
      S2990DFpd (S2990FFpd a b c) 0 0.
Theorem S3034_hscalar_iff (logQ a b c) :
  S3034Hscalar R ... D logQ a b c <->
    -actualC3LogShellTensorLogVolume
      (S2717C3 R ... D) <=
      CThetaPaper fiveLabel logQ 0 S2990DFpd (S2990FFpd a b c) 0 0 *
        paperQAbsLog fiveLabel logQ.
There is no theorem giving S3034Hscalar; it is a Prop target. Its conclusion is
an UPPER bound on the negative C3 tensor log-volume, i.e. -V_C3 <= CTheta*A.
It is not a lower bound on rhs and no theorem identifies -V_C3 with rhs or R.

### S3016CThetaUpperActual
Structure S3016CThetaUpperInterface (T : SourceNativeInitialThetaData) a b c:
  stepVLogMagnitude : Real
  stepVLogMagnitude_eq : stepVLogMagnitude = S3016StepVQPilot a b c
  globalLogMagnitude : Real
  globalLogMagnitude_eq : globalLogMagnitude = S3016WeightedGlobalQPilot T
  identification : stepVLogMagnitude = globalLogMagnitude
  thetaSigned : Real
  cthetaPaper : Real
  upper : thetaSigned <= cthetaPaper * |stepVLogMagnitude|.
Theorems:
  stepV_eq_global (I) : S3016StepVQPilot a b c = weightedGlobal.
  upper_bound (I) : thetaSigned <= cthetaPaper * |S3016StepVQPilot a b c|.
The identification and the upper bound are FIELDS of the interface. There is no
construction of the interface, no proof of identification, and no relation
between thetaSigned/stepVLogMagnitude and the lana/our rhs or A. In particular,
the interface gives an upper bound on a chosen thetaSigned, not rhs >= -A.

### S3017StepVUpperGapAssembly
S3017_processionAverage_bound / _expanded: restate S3014 average bound for
S3014ProcessionData; PARTIAL.
S3017_CTheta_upper_of_height (n hn hheight a b c habc) :
  Height.logHeight1 (abcJInvariant a b c) <= S3015FinalBound n a b c
where hheight is exactly:
  forall a b c, IsABCTriple a b c ->
    Height.logHeight1 (abcJInvariant a b c) <=
      (1/n) * sum_{j in Icc 1 n}
        StepVProcessionAverage.collectionBound
          (2*n+1) S2921D (S2921Q a b c) (S2921S a b c) (S2921T a b c) j.
This is an upper bound on an analytic height, not on rhs; hheight is an explicit
argument, not proved.

## 2. Is hheight green?

hheight is the pointwise statement S2921HeightLeProcessionPointwise n
(S2921HeightBridgeActual.lean:61), defined as the same forall a b c height
inequality with S2921D/S2921Q/S2921S/S2921T.

Status:
- S2921HeightBridgeActual builds actual candidate definitions S2921D,
  S2921Q, S2921S, S2921T and proves S2921Q_eq_regionVolume,
  S2921D_nonneg, S2921_hweightvol_candidate.
- It explicitly records the "First error / exact mismatch": Q,S,T are
  triple-dependent while S2920HeightLeProcession has fixed constants; missing
  uniform global bounds Qconst/Sconst/Tconst and the height-to-collection
  identification. No theorem proves S2921HeightLeProcessionPointwise.
- S3015FinalRealInequalityActual.S3015_final_real_inequality takes exactly this
  hheight as an explicit hypothesis; it is not discharged.
Therefore hheight is NOT green; it is an open premise.

## 3. Can N5Weak be derived from upper_bound + hheight?

No, for three independent reasons.

(a) Direction. N5Weak is rhs >= -A (a LOWER bound on rhs / upper bound on R).
  S3034_hscalar_iff gives -V_C3 <= CTheta*A (an UPPER bound on -V_C3);
  even if one identified V_C3 = -rhs, this would give rhs <= CTheta*A, not
  rhs >= -A. It points the opposite way.
  S3016CThetaUpperInterface.upper_bound gives thetaSigned <= CTheta*|stepV|;
  again an upper bound on a theta scalar, not a lower bound on rhs.
  S3017_CTheta_upper_of_height gives an upper bound on logHeight1; no relation
  to rhs.

(b) No identification. There is no theorem in S3034/S3016/S3017 connecting
  actualC3LogShellTensorLogVolume, thetaSigned, S3015FinalBound, or
  S3016StepVQPilot to rhs, R, or A of the Cor312VariantData. They live in
  different interfaces; the exact bridge S3019MissingBridge (qPilot line bundle
  vs native weighted sum) is itself unproved (N5-ASSEMBLY-INVENTORY).

(c) Missing lower-bound hypothesis. To get N5Weak one needs either:
  - a theorem -A <= rhs directly (variant/SS), or
  - an upper bound R <= A, or
  - a lower bound on logVol(hull)/theta hull.
  None of S3034/S3016CTheta/S3017 supplies a lower bound. hheight supplies an
  upper bound on height, not one of these quantities.

## 4. Minimal additional assumptions to make a conditional N5Weak

If one wants a conditional theorem, the minimal named assumptions are:
1. actual identification R_C3 = -rhs (or V_C3 = -rhs) tying the C3 tensor
   volume to rhsData.rhs;
2. S3019MissingBridge or S3016IdentificationTarget to identify the StepV
   q-pilot with the global/native q-pilot;
3. a LOWER bound for rhs (or -A <= rhs), i.e. the variant/SS itself; the
   upper_bound fields are insufficient;
4. hheight, if the S3015 height bound is used; hheight is open.
Even with 1-4, the conclusion would be a conditional N5Weak, not an
unconditional one.

## 5. Verdict

- S3034_hscalar_iff: exact equivalence, but to an UPPER bound on -V_C3.
- S3016CThetaUpperInterface: exact interface; identification and upper are
  fields, no construction, no rhs/A connection.
- S3017_CTheta_upper_of_height: valid theorem but conditional on hheight, and
  concludes an upper height bound.
- hheight is the unproved S2921HeightLeProcessionPointwise; S2921 itself records
  the fixed-vs-triple-dependent and height-vs-collection mismatches.
- Therefore N5Weak is NOT derivable from upper_bound + hheight, neither
  unconditionally nor by direction alone. The upper-bound stack cannot produce
  the required lower bound on rhs; the missing object is still the variant/SS
  (or an equivalent R <= A) plus the actual C3/rhs identification.

No Lean file written; no compile claimed.
