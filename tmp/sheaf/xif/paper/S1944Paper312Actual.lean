import tmp.sheaf.xif.paper.S1940PaperLStarDeterminantActual
import tmp.sheaf.xif.paper.S1905Unconditional312Actual
import tmp.sheaf.xif.paper.S1880OriginalXiFActual
import tmp.sheaf.xif.paper.S1928BridgeAverageA0Actual

/-!
# S1944: the paper-level Corollary 3.12 at the actual S1940 l* source
determinant, and the exact first missing of the S1905 (q = 1/5 model) chain

Layer: O (original-text Theta-link / IUT III Corollary 3.12, Step (xi-f)).

## What this file does

S1940 built the actual paper l* source determinant

  s1940PaperLStarDeterminant T : SignedHullLogActual (SignedLabel l.value)

from the actual S1902 normalized Haar hull mass (clipped at one by the
signed-hull normalization 1 <= scale; its logarithm is the S1915 readout a0)
and proved the S1904 procession bridge unconditionally:

  s1940_s1904_bridge :
    S1904ProcessionBridge (s1902ActualThetaHull T)
      (s1940PaperLStarDeterminant T).

S1905 built the paper signed-hull datum S1905D from the S1902 theta hull and
the S1903 determinant s1903ActualDeterminant l, whose third field is the
proposition S1905FirstMissing T : S1904ProcessionBridge (S1905ThetaHull T)
(S1905Determinant).  S1928 computed that this S1903 determinant is the
q = 1/5 *model* determinant (average = log 5 * sum_j j^2 / l^4) and that the
bridge there is exactly the arithmetic identity S1928ArithmeticIdentity T;
it is false at least on the clipped region s1915ClosedForm T <= 0
(s1928_bridge_false_of_closedForm_nonpos).

Consequently the literal term S1905D T s1940_s1904_bridge is *ill-typed*:
the hypothesis of S1905D T is the bridge at s1903ActualDeterminant l, while
the S1940 bridge is the bridge at the different paper determinant
s1940PaperLStarDeterminant T.  This file therefore:

1. defines the type-correct paper analogue of the S1905 first missing at the
   actual paper determinant,

     S1944FirstMissing T :=
       S1904ProcessionBridge (s1902ActualThetaHull T)
         (s1940PaperLStarDeterminant T),

   and proves it is a theorem (section 1);

2. assembles the paper signed-hull datum

     S1944D T : OrigXiFPaperSignedHullData (S1902Carrier T) l

   with thetaHull = s1902ActualThetaHull T, determinant =
   s1940PaperLStarDeterminant T, third field = s1940_s1904_bridge T
   (section 2);

3. identifies its signed hull log-volume: it is -a0, i.e. minus the actual
   S1915 readout max 0 (s1915ClosedForm T); in particular it is 0 on the
   clipped region and -s1915ClosedForm T on the unclipped region (section 3);

4. proves the paper 3.12 inequality

     -|log q| <= OrigXiFSignedThetaHullLogVolume (S1944D T)

   through S1880 (s1880_xiF_inequality_abs), in both the -|log q| and the
   localLogMagnitude forms, and also proves the same inequality at the old
   S1905 datum whenever its missing hypothesis is supplied (section 4).  The
   inequality also holds for the direct -a0 value of section 3;

5. proves the ray membership and the ray/link identifications at S1944D T
   (section 5): the paper ray R_{<= -|log Theta|} contains -|log q|, the
   ThetaLinkRayObligation (the exact consumer field of
   ThetaLinkActual.link_implies_inclusion) holds, and S1880's concrete
   link_identification of the paper-route Theta-link holds at S1944D T
   for every supply R of the paper's remaining Definition 3.1 clauses
   (with its q-pilot scalar in the ray);

6. proves the exact first missing of the S1905 chain (section 6): the S1905
   first missing is *equivalent* to S1928ArithmeticIdentity T and to its
   explicit scaled/log 5 forms, it is not a theorem of the two actual S1902/
   S1903 structures, and it is *false* on the clipped region.  The corresponding
   datum at the S1903 model determinant exists iff the arithmetic identity.
   So S1905's first missing is a property of the discarded q = 1/5 model
   determinant, not of the paper l* determinant; at the paper determinant the
   first missing is closed by S1940.

## Boundary and honesty

The S1940 determinant is not the S1903 q = 1/5 model determinant: their
procession averages differ on the clipped region (0 versus
log 5 * sum_j j^2 / l^4 > 0), so the two bridge propositions are genuinely
different and no bridge hypothesis is transported between them.  The S1905
first missing is *not* asserted as a theorem here; it is exactly the arithmetic
identity S1928 isolated.  On the S1944 datum the three-field structure and all
downstream S1880/S1905 conclusions are unconditional.

No sorry, admit, axiom, True/PUnit slot, fake Haar measure, fake hull, or
arbitrary datum is used.  The only local instances are the standard
irreducibility of X^2 + 1 over Q and primality of 5, needed to read the
actual completion q exactly as in S1487/S1880/S1938.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1944Paper312Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1903SignedHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1905Unconditional312Actual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1928BridgeAverageA0Actual
open LeanFormal.IUT.XiFPaper.S1940PaperLStarDeterminantActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaperThetaHull
open scoped BigOperators

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

/-- The concrete Gaussian field Q(i) is an AdjoinRoot, so its Field instance
needs the irreducibility fact; this is the same local instance as in
S1487/S1880/S1938 when reading the actual completion q. -/
local instance s1944GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1944FivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The paper theta hull, the paper determinant, and the paper first
missing -/

/-- The theta hull of the paper datum: the actual S1902 1,circ U hull on the
root-extension product carrier (the same hull as S1905ThetaHull). -/
abbrev S1944ThetaHull : ActualThetaHull (S1902Carrier T) l :=
  s1902ActualThetaHull T

/-- The determinant of the paper datum: the actual paper l* source determinant
of S1940, built from the actual S1902 normalized Haar hull mass (clipped at
one) with the S1915 readout a0. -/
abbrev S1944Determinant : SignedHullLogActual (SignedLabel l.value) :=
  s1940PaperLStarDeterminant T

/-- **The S1905-shaped first missing at the actual paper determinant.**  It is
literally the third field of OrigXiFPaperSignedHullData at the S1902 hull and
the S1940 paper l* determinant. -/
def S1944FirstMissing : Prop :=
  S1904ProcessionBridge (S1944ThetaHull T) (S1944Determinant T)

/-- The paper first missing is the procession bridge at the actual S1902 hull
and the actual paper l* determinant. -/
theorem S1944FirstMissing_iff :
    S1944FirstMissing T ↔
      S1904ProcessionBridge (s1902ActualThetaHull T)
        (s1940PaperLStarDeterminant T) :=
  Iff.rfl

/-- The paper first missing is the explicit Haar readout equation. -/
theorem S1944FirstMissing_iff_logVolume :
    S1944FirstMissing T ↔
      (S1944ThetaHull T).haar.logVolume
          (S1944ThetaHull T).compactHull.hull =
        ENNReal.ofReal (S1944Determinant T).procession.average :=
  Iff.rfl

/-- **The paper first missing is proved unconditionally** by the S1940
procession bridge.  This is the exact S1905 third field at the paper
determinant. -/
theorem s1944_firstMissing : S1944FirstMissing T :=
  s1940_s1904_bridge T

/-! ## 2. The paper signed-hull datum -/

/-- **The actual paper signed-hull datum** OrigXiFPaperSignedHullData at the
S1902 theta hull and the S1940 paper l* determinant.  Its third field is the
proved S1940 bridge, so the datum is inhabited unconditionally. -/
noncomputable def S1944D : OrigXiFPaperSignedHullData (S1902Carrier T) l where
  thetaHull := S1944ThetaHull T
  determinant := S1944Determinant T
  hull_logVolume_eq_procession := s1940_s1904_bridge T

@[simp] theorem S1944D_thetaHull :
    (S1944D T).thetaHull = S1944ThetaHull T := rfl

@[simp] theorem S1944D_determinant :
    (S1944D T).determinant = S1944Determinant T := rfl

/-- The third field of the paper datum is the S1940 bridge. -/
theorem S1944D_hull_logVolume_eq_procession :
    (S1944D T).hull_logVolume_eq_procession = s1940_s1904_bridge T := rfl

/-- The paper datum has the S1902 theta hull. -/
theorem S1944D_thetaHull_eq_s1902 :
    (S1944D T).thetaHull = s1902ActualThetaHull T := rfl

/-- The paper datum has the S1940 paper l* determinant. -/
theorem S1944D_determinant_eq_s1940 :
    (S1944D T).determinant = s1940PaperLStarDeterminant T := rfl

/-- The bridge datum proposition holds at the paper datum. -/
theorem s1944D_bridgeDatum : S1904ProcessionBridgeDatum (S1944D T) :=
  s1940_s1904_bridge T

/-- **The paper signed-hull datum exists unconditionally** with exactly the
S1902 hull and the S1940 paper l* determinant. -/
theorem s1944_paper_datum_exists :
    ∃ D : OrigXiFPaperSignedHullData (S1902Carrier T) l,
      D.thetaHull = s1902ActualThetaHull T ∧
        D.determinant = s1940PaperLStarDeterminant T :=
  ⟨S1944D T, rfl, rfl⟩

/-! ## 3. The signed hull log-volume of the paper datum -/

/-- The paper determinant's procession average is the actual S1915 readout a0
(equivalently, the paper bridge is the identity average = a0). -/
theorem s1944D_average :
    (S1944D T).determinant.procession.average = s1915A0 T :=
  (s1915_bridge_iff_average_eq_a0 (T := T)
    (P := S1944Determinant T)).mp (s1940_s1904_bridge T)

/-- **The signed hull log-volume of the paper datum is -a0.** -/
theorem s1944D_signed_eq_neg_a0 :
    OrigXiFSignedThetaHullLogVolume (S1944D T) = -s1915A0 T := by
  rw [OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  exact congrArg Neg.neg (s1944D_average T)

/-- On the unclipped region the signed hull log-volume is minus the actual
closed form 1 + sum_b [K_b : Q_p] * log (rootImageRadius T b). -/
theorem s1944D_signed_eq_neg_closedForm
    (h : 0 <= s1915ClosedForm T) :
    OrigXiFSignedThetaHullLogVolume (S1944D T) = -s1915ClosedForm T := by
  rw [s1944D_signed_eq_neg_a0, s1915_a0_eq_closedForm T h]

/-- On the clipped region the signed hull log-volume is exactly zero. -/
theorem s1944D_signed_eq_zero_of_clipped
    (h : s1915ClosedForm T <= 0) :
    OrigXiFSignedThetaHullLogVolume (S1944D T) = 0 := by
  rw [s1944D_signed_eq_neg_a0, s1915_a0_eq_zero_of_closedForm_nonpos T h,
    neg_zero]

/-- The paper datum's signed hull log-volume is nonpositive. -/
theorem s1944D_signed_nonpos :
    OrigXiFSignedThetaHullLogVolume (S1944D T) <= 0 := by
  rw [s1944D_signed_eq_neg_a0]
  exact neg_nonpos.mpr (s1915_a0_nonneg T)

/-- The paper datum's signed hull log-volume is at least -1, the paper's
-|log Theta| >= -1 normalization. -/
theorem s1944D_signed_ge_neg_one :
    -1 <= OrigXiFSignedThetaHullLogVolume (S1944D T) := by
  rw [s1944D_signed_eq_neg_a0]
  have h := s1915_a0_le_one T
  linarith

/-- The signed hull log-volume of the paper signed hull built from S1944D is
also -a0. -/
theorem s1944D_paperSignedHull_signedHullLogVolume :
    (OrigXiFPaperSignedHull (S1944D T)).signedHullLogVolume = -s1915A0 T := by
  rw [OrigXiFPaperSignedHull_signedHullLogVolume, s1944D_signed_eq_neg_a0]

/-! ## 4. The paper Corollary 3.12 inequality at the paper datum -/

/-- **The paper 3.12 inequality** -|log q| <= -|log Theta| at the actual
paper l* determinant, from S1880. -/
theorem s1944_paper312_inequality :
    -|Real.log ‖S1487Cand.q‖| <=
      OrigXiFSignedThetaHullLogVolume (S1944D T) :=
  s1880_xiF_inequality_abs (S1944D T)

/-- The same comparison in the paper's localLogMagnitude form. -/
theorem s1944_paper312_inequality_magnitude :
    -localLogMagnitude S1487Cand <=
      OrigXiFSignedThetaHullLogVolume (S1944D T) :=
  s1880_xiF_inequality (S1944D T)

/-- The comparison is strict: -|log q| < -|log Theta|. -/
theorem s1944_paper312_strict :
    -|Real.log ‖S1487Cand.q‖| <
      OrigXiFSignedThetaHullLogVolume (S1944D T) :=
  s1880_xiF_inequality_strict (S1944D T)

/-- The explicit numerical form of the paper inequality: -|log q| <= -a0. -/
theorem s1944_paper312_inequality_neg_a0 :
    -|Real.log ‖S1487Cand.q‖| <= -s1915A0 T := by
  rw [← s1944D_signed_eq_neg_a0]
  exact s1944_paper312_inequality T

/-- **The 3.12 inequality at the old S1905 datum**, whenever its first missing
hypothesis is supplied: the witness is used only to form the datum, and S1880
gives the comparison unconditionally in the datum. -/
theorem s1944_paper312_inequality_S1905D (h : S1905FirstMissing T) :
    -|Real.log ‖S1487Cand.q‖| <=
      OrigXiFSignedThetaHullLogVolume (S1905D T h) :=
  s1880_xiF_inequality_abs (S1905D T h)

/-- The paper inequality at the paper datum, bundled with the exact value of
the signed hull log-volume. -/
theorem s1944_paper312_package :
    OrigXiFSignedThetaHullLogVolume (S1944D T) = -s1915A0 T ∧
      -|Real.log ‖S1487Cand.q‖| <=
        OrigXiFSignedThetaHullLogVolume (S1944D T) :=
  ⟨s1944D_signed_eq_neg_a0 T, s1944_paper312_inequality T⟩

/-! ## 5. The paper ray and the Theta-link identifications -/

/-- **The paper ray membership**: -|log q| lies in the ray
R_{<= -|log Theta|} of the actual paper signed hull built from S1944D. -/
theorem s1944_ray :
    -|Real.log ‖S1487Cand.q‖| ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull (S1944D T)).signedHullLogVolume :=
  s1880_xiF_paperSignedHullRay (S1944D T)

/-- The ThetaLinkRayObligation at the paper datum: this is literally the
proposition type of the consumer field
ThetaLinkActual.link_implies_inclusion. -/
theorem s1944_thetaLinkRay :
    OrigXiFThetaLinkRayObligation (S1944D T)
      (-|Real.log ‖S1487Cand.q‖|) :=
  (OrigXiFThetaLinkRayObligation_iff (S1944D T) _).mpr
    (s1944_paper312_inequality T)

/-- Ray membership is exactly the paper signed-hull inequality. -/
theorem s1944_ray_iff_inequality :
    (-|Real.log ‖S1487Cand.q‖| ∈
        hullLogVolumeRay
          (OrigXiFPaperSignedHull (S1944D T)).signedHullLogVolume) ↔
      -|Real.log ‖S1487Cand.q‖| <=
        OrigXiFSignedThetaHullLogVolume (S1944D T) :=
  OrigXiFThetaLinkRay_iff_le (S1944D T) _

/-- The hullLogVolumeRay of the paper signed hull is the paper theta-hull
log-volume ray of the paper datum. -/
theorem s1944_hullLogVolumeRay_eq :
    hullLogVolumeRay (OrigXiFPaperSignedHull (S1944D T)).signedHullLogVolume =
      OrigXiFThetaHullLogVolumeRay (S1944D T) :=
  OrigXiFPaperSignedHull_hullLogVolumeRay_eq (S1944D T)

/-- **The concrete link identification of the paper-route Theta-link at the
paper datum**, for every supply R of the paper's remaining Definition 3.1
clauses.  This is S1880's link_identification specialised to the S1944 paper
signed-hull datum. -/
theorem s1944_paper_linkIdentification
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (s1880_paper_thetaLink l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
      (S1944D T)).link_identification :=
  s1880_paper_linkIdentification l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat (S1944D T)

/-- **The paper-route xi-f ray at the paper datum**: the q-pilot scalar of the
paper-route object lies in the ray of the S1944 paper signed hull. -/
theorem s1944_paper_xiF_ray
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1880PaperO l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull (S1944D T)).signedHullLogVolume :=
  s1880_paper_xiF_ray l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat (S1944D T)

/-! ## 6. The exact first missing of the S1905 (q = 1/5 model) chain

The literal S1905D T s1940_s1904_bridge is not well-typed: S1905FirstMissing
is the bridge at the S1903 model determinant, not at the paper determinant.
The S1905 first missing is *exactly* the S1928 arithmetic identity and is false
on the clipped region; it is not a first missing of the paper chain, whose
datum is S1944D. -/

/-- **The exact first missing of the S1905 chain**: S1905FirstMissing T is
equivalent to the S1928 arithmetic identity at the actual S1902/S1903 fields. -/
theorem s1944_S1905FirstMissing_iff_identity :
    S1905FirstMissing T ↔ S1928ArithmeticIdentity T :=
  s1928_s1905FirstMissing_iff T

/-- The exact first missing in the explicit scaled real form: twice l plus the
actual local qVFamily log-sum equals the rational multiple of log 5. -/
theorem s1944_S1905FirstMissing_iff_scaled :
    S1905FirstMissing T ↔
      2 * (l.value : Real) +
          ∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
            (s1915LocalDegree T b : Real) *
              Real.log ‖(sourceRootQUnit T b : rootBase T b)‖
        = 2 * (l.value : Real) * Real.log 5 *
            (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) /
              ((l.value : Real) ^ 4) :=
  s1928_s1905FirstMissing_iff_scaled T

/-- The exact first missing as an identification of log 5 with the actual local
qVFamily data. -/
theorem s1944_S1905FirstMissing_iff_log_five :
    S1905FirstMissing T ↔
      Real.log 5 =
        (2 * (l.value : Real) +
            ∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
              (s1915LocalDegree T b : Real) *
                Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) /
          (2 * (l.value : Real) *
            (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) /
              ((l.value : Real) ^ 4)) := by
  rw [s1944_S1905FirstMissing_iff_identity]
  exact s1928_identity_iff_log_five (T := T)

/-- **The S1905 first missing is false on the clipped region**
s1915ClosedForm T <= 0: there a0 = 0 while the S1903 model determinant
average is positive. -/
theorem s1944_S1905FirstMissing_false_of_clipped
    (h : s1915ClosedForm T <= 0) :
    ¬ S1905FirstMissing T :=
  s1928_bridge_false_of_closedForm_nonpos T h

/-- The S1905 first missing is not derivable from the two actual structures:
for every actual theta hull there is an actual determinant at which the bridge
fails (S1904), so it is genuine additional data. -/
theorem s1944_S1905FirstMissing_not_derivable
    (T' : ActualThetaHull (S1902Carrier T) l) :
    ∃ P : SignedHullLogActual (SignedLabel l.value),
      ¬ S1904ProcessionBridge T' P :=
  s1904_bridge_not_derivable T'

/-- **The datum at the S1903 model determinant exists iff the arithmetic
identity**: a paper signed-hull datum with the S1902 hull and the S1903 model
determinant exists exactly when S1928ArithmeticIdentity T holds. -/
theorem s1944_S1905D_exists_iff_identity :
    (∃ D : OrigXiFPaperSignedHullData (S1902Carrier T) l,
        D.thetaHull = S1905ThetaHull T ∧
          D.determinant = S1905Determinant (l := l)) ↔
      S1928ArithmeticIdentity T :=
  (s1905_firstMissing_iff_exists_datum T).symm.trans
    (s1928_s1905FirstMissing_iff T)

/-- **At the paper determinant the first missing is closed, while at the S1903
model determinant it is not** on the clipped region. -/
theorem s1944_paper_bridge_and_model_bridge_ne
    (h : s1915ClosedForm T <= 0) :
    S1944FirstMissing T ∧ ¬ S1905FirstMissing T :=
  ⟨s1944_firstMissing T, s1944_S1905FirstMissing_false_of_clipped T h⟩

/-- **The two bridge propositions are not interchangeable**: on the clipped
region the paper bridge at the S1940 determinant holds while the bridge at the
S1903 model determinant fails, so the S1944 first missing is not equivalent to
the S1905 first missing. -/
theorem s1944_paper_firstMissing_not_iff_model
    (h : s1915ClosedForm T <= 0) :
    ¬ (S1944FirstMissing T ↔ S1905FirstMissing T) := by
  intro hiff
  exact (s1944_S1905FirstMissing_false_of_clipped T h)
    (hiff.mp (s1944_firstMissing T))

/-- On the clipped region the paper l* determinant and the S1903 q = 1/5 model
determinant are genuinely different: their procession averages are 0 and a
positive multiple of log 5. -/
theorem s1944_determinants_ne_of_clipped
    (h : s1915ClosedForm T <= 0) :
    s1940PaperLStarDeterminant T ≠ s1903ActualDeterminant l := by
  intro hD
  have h1 : (s1940PaperLStarDeterminant T).procession.average = 0 := by
    rw [show (s1940PaperLStarDeterminant T).procession.average = s1915A0 T from
      s1940PaperLStarDeterminant_processionNormalized T]
    exact s1915_a0_eq_zero_of_closedForm_nonpos T h
  rw [hD] at h1
  have h2 : 0 < (s1903ActualDeterminant l).procession.average :=
    s1928_average_pos (l := l)
  linarith

/-- **The paper-level package at the S1940 paper l* determinant**: the datum
exists, its signed hull log-volume is -a0, the Corollary 3.12 inequality
holds, and -|log q| lies in the paper ray. -/
theorem s1944_paper_chain :
    ∃ D : OrigXiFPaperSignedHullData (S1902Carrier T) l,
      D.thetaHull = s1902ActualThetaHull T ∧
        D.determinant = s1940PaperLStarDeterminant T ∧
          OrigXiFSignedThetaHullLogVolume D = -s1915A0 T ∧
            -|Real.log ‖S1487Cand.q‖| <=
                OrigXiFSignedThetaHullLogVolume D ∧
              -|Real.log ‖S1487Cand.q‖| ∈
                hullLogVolumeRay
                  (OrigXiFPaperSignedHull D).signedHullLogVolume :=
  ⟨S1944D T, rfl, rfl, s1944D_signed_eq_neg_a0 T,
    s1944_paper312_inequality T, s1944_ray T⟩

/-! ## 7. Axiom probes -/

#print axioms s1944_firstMissing
#print axioms S1944D
#print axioms s1944D_average
#print axioms s1944D_signed_eq_neg_a0
#print axioms s1944D_signed_eq_zero_of_clipped
#print axioms s1944_paper312_inequality
#print axioms s1944_paper312_inequality_magnitude
#print axioms s1944_paper312_strict
#print axioms s1944_paper312_inequality_neg_a0
#print axioms s1944_ray
#print axioms s1944_thetaLinkRay
#print axioms s1944_ray_iff_inequality
#print axioms s1944_paper_linkIdentification
#print axioms s1944_paper_xiF_ray
#print axioms s1944_S1905FirstMissing_iff_identity
#print axioms s1944_S1905FirstMissing_iff_scaled
#print axioms s1944_S1905FirstMissing_iff_log_five
#print axioms s1944_S1905FirstMissing_false_of_clipped
#print axioms s1944_S1905D_exists_iff_identity
#print axioms s1944_paper_bridge_and_model_bridge_ne
#print axioms s1944_paper_firstMissing_not_iff_model
#print axioms s1944_determinants_ne_of_clipped
#print axioms s1944_paper_chain

end LeanFormal.IUT.XiFPaper.S1944Paper312Actual

end
