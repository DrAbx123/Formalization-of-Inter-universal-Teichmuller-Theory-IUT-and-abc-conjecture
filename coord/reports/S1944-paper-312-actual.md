# S1944: the paper-level Corollary 3.12 at the actual S1940 l* determinant, and the exact S1905 first missing

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1944Paper312Actual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1944Paper312Actual.olean

## Verification

- Build command: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1944Paper312Actual.olean tmp/sheaf/xif/paper/S1944Paper312Actual.lean
- EXIT=0, 0 errors, 0 warnings; the log contains only the axiom probes.
- Source SHA256: B094D5A411E22E9F6DF7F96D4DB012DDC359F4354F1FEA0EFEE3A14324B2B836
- Source bytes: 23756
- Olean SHA256: 61B7231D9F6EC41FCC8BD1E36FB5A1D45BF7C9C2EC0E714EA16ABCB97E25A22F
- Olean bytes: 211416
- All 23 #print axioms entries report only [propext, Classical.choice, Quot.sound];
  no sorryAx, no axiom declaration, no True/PUnit slot.
- Import re-check: tmp/sheaf/xif/paper/_S1944Consumer.lean imports the olean,
  #checks all 24 main declarations and reprints four axiom sets; EXIT=0, no
  errors, no warnings (log: tmp/sheaf/xif/paper/_S1944_consumer.log).

## Result

The type-correct paper analogue of the S1905 first missing at the actual S1940
paper l* determinant

  S1944FirstMissing T :=
    S1904ProcessionBridge (s1902ActualThetaHull T)
      (s1940PaperLStarDeterminant T)

is a theorem (s1944_firstMissing, from s1940_s1904_bridge), and the paper
signed-hull datum

  S1944D T : OrigXiFPaperSignedHullData (S1902Carrier T) l

is assembled with thetaHull = s1902ActualThetaHull T, determinant =
s1940PaperLStarDeterminant T, third field = s1940_s1904_bridge T.  The literal
term S1905D T s1940_s1904_bridge is ill-typed because S1905FirstMissing is the
bridge at s1903ActualDeterminant l (the S1928 q = 1/5 model determinant), not
at the paper determinant; S1944D is the type-correct assembly.

## What is proved unconditionally

1. [PROVED] s1944_firstMissing: S1944FirstMissing T at the actual paper l*
   determinant.
2. [BUILT] S1944D, s1944_paper_datum_exists: the paper signed-hull datum
   exists with exactly the S1902 hull and the S1940 determinant.
3. [PROVED] s1944D_average: determinant procession average = s1915A0 T;
   s1944D_signed_eq_neg_a0: OrigXiFSignedThetaHullLogVolume (S1944D T) = -a0;
   s1944D_signed_eq_neg_closedForm on 0 <= s1915ClosedForm T;
   s1944D_signed_eq_zero_of_clipped on s1915ClosedForm T <= 0;
   s1944D_signed_nonpos, s1944D_signed_ge_neg_one;
   s1944D_paperSignedHull_signedHullLogVolume.
4. [PROVED] The paper 3.12 inequality through S1880:
   s1944_paper312_inequality (-|log q| <= OrigXiFSignedThetaHullLogVolume (S1944D T)),
   s1944_paper312_inequality_magnitude (localLogMagnitude form),
   s1944_paper312_strict (strict),
   s1944_paper312_inequality_neg_a0 (explicit -|log q| <= -a0),
   and s1944_paper312_inequality_S1905D at the old S1905 datum whenever its
   missing hypothesis is supplied.
5. [PROVED] The ray and link identifications at S1944D:
   s1944_ray (paper ray membership of -|log q|),
   s1944_thetaLinkRay (OrigXiFThetaLinkRayObligation, the exact consumer field
   type of ThetaLinkActual.link_implies_inclusion),
   s1944_ray_iff_inequality, s1944_hullLogVolumeRay_eq,
   s1944_paper_linkIdentification (S1880 concrete link_identification at
   S1944D for every paper clause supply R),
   s1944_paper_xiF_ray (paper-route q-pilot scalar in the S1944 ray).
6. [PROVED] The exact first missing of the S1905 chain:
   s1944_S1905FirstMissing_iff_identity: S1905FirstMissing T <-> S1928ArithmeticIdentity T;
   s1944_S1905FirstMissing_iff_scaled: the explicit real equation
     2l + sum_b [K_b : Q_p] log||q_b|| = 2l * log 5 * (sum_j j^2)/l^4;
   s1944_S1905FirstMissing_iff_log_five: the log 5 identification;
   s1944_S1905FirstMissing_false_of_clipped: false on s1915ClosedForm T <= 0;
   s1944_S1905FirstMissing_not_derivable (S1904 non-derivability);
   s1944_S1905D_exists_iff_identity: a datum with the S1903 model determinant
   exists iff the arithmetic identity;
   s1944_paper_bridge_and_model_bridge_ne, s1944_paper_firstMissing_not_iff_model:
   the two bridge propositions are not interchangeable on the clipped region;
   s1944_determinants_ne_of_clipped: the two determinants are genuinely
   different there (average 0 versus log 5 * sum_j j^2 / l^4 > 0);
   s1944_paper_chain: the whole paper package (datum, signed volume -a0,
   3.12 inequality, ray membership).

## Exact first missing after S1944

None for the paper-faithful chain at the S1940 l* determinant: the three-field
datum is inhabited and its procession bridge, the 3.12 inequality and the
Theta-link ray are theorems.

The S1905 first missing is exactly the S1928 arithmetic identity
(S1928ArithmeticIdentity T), an identification of log 5 with the actual local
qVFamily log-norms at the bad places.  It is not a first missing of the paper
chain: it belongs to the discarded S1903 q = 1/5 model determinant, and it is
already false wherever s1915ClosedForm T <= 0 (there a0 = 0 while the S1903
average is positive).  The S1928 file records the stronger Lindemann-Weierstrass
argument that the identity is false for the actual pair; that argument is not
formalized in the tree.

## Boundary kept explicit

- The S1940 bridge is used as an input theorem (proved in
  S1940PaperLStarDeterminantActual); this file does not re-prove it.
- The S1940 determinant and the S1903 model determinant are different objects;
  no bridge hypothesis is transported between them, and the ill-typed term
  S1905D T s1940_s1904_bridge is replaced by the explicit datum S1944D.
- The remaining paper-level input types (D5 torsion clause and the other
  Definition 3.1 clause supply fields) are unchanged and out of scope; the
  link identification is stated for every supply R, exactly as in S1880.
- The 3.12 inequality is also available at any actual datum via S1880
  (s1880_xiF_inequality_abs); here it is instantiated at S1944D.

## Axioms

propext, Classical.choice, Quot.sound only (all 23 probes).
