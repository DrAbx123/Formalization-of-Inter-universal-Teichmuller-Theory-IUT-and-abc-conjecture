# S1158: concrete square attempt from I.fPrimeStripAt / I.fLinkAt

Read: S1151 report, SourceH1H2Construction, SourceFTimesMuPrimeStripPolyIsomorphism.

## 1. Actual reusable data

SourceH1H2Construction provides:
  I.fPrimeStripAt (n m : Int) : FPrimeStrip V
  I.fLinkAt n m n' m' : FPrimeStripEquiv (I.fPrimeStripAt n m) (I.fPrimeStripAt n' m')

SourceFTimesMuPrimeStripPolyIsomorphism provides:
  SourceFTimesMuPrimeStrip.canonical F
  SourceFTimesMuPrimeStripEquivalence.canonicalLift (fLinkAt ...)
  SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
  SourceFTimesMuPrimeStripFullPolyIsomorphism.canonical_trans
  SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc

## 2. Natural candidate construction

Choose the rectangle of lattice points
  (n,m) --- (n,m+1)
    |           |
  (n+1,m) - (n+1,m+1)

Define four vertices (canonical times-mu strips):
  A = canonical (I.fPrimeStripAt n m)
  B = canonical (I.fPrimeStripAt n (m+1))
  C = canonical (I.fPrimeStripAt (n+1) m)
  D = canonical (I.fPrimeStripAt (n+1) (m+1))

Define the four arrows by canonical lifts of the actual F-links:
  upperEnv  = ofEquivalence (canonicalLift (I.fLinkAt n m n (m+1)))       : A -> B
  lowerEnv  = ofEquivalence (canonicalLift (I.fLinkAt (n+1) m (n+1) (m+1))) : C -> D
  leftVert  = ofEquivalence (canonicalLift (I.fLinkAt n m (n+1) m))       : A -> C
  rightVert = ofEquivalence (canonicalLift (I.fLinkAt n (m+1) (n+1) (m+1))) : B -> D

## 3. What actually works

The four arrows are actual full poly-isomorphisms (Quotient of the naturally
isomorphic setoid).  If the underlying F-link paths are equal,
  trans (I.fLinkAt n m (n+1) m) (I.fLinkAt (n+1) m (n+1) (m+1))
  =
  trans (I.fLinkAt n m n (m+1)) (I.fLinkAt n (m+1) (n+1) (m+1)),
then canonical_trans proves the commutation
  leftVert . lowerEnv = upperEnv . rightVert.

This is an actual canonical-link square.  It is not yet the Remark 3.10.2
square: upperEnv here is a canonical lift of an F-link, while the paper's
upperEnv is the etale-like evaluation isomorphism with Kummer/evaluation
provenance; leftVert/rightVert here are F-link lifts, not the Kummer
isomorphisms verticalEnv/verticalGau.

## 4. First exact missing source evaluation sublemma

The first gap is not path equality; it is provenance of the upper horizontal.
The exact missing sublemma is an actual full poly-isomorphism
  upperEnv : canonical (I.fPrimeStripAt n m) -> canonical (I.fPrimeStripAt n' m')
whose underlying arrow is source etale-like evaluation, together with the two
Kummer verticals and the Kummer/evaluation square commutation.

Equivalently, the first missing datum is an inhabitant of
  ThetaLinkLogKummerActual.ThetaLinkSquareData
whose upper horizontal is upperEnv and whose left/right verticals are the
Kummer isomorphisms.  The existing ThetaLinkFactorizationData and
ThetaLinkSquareData structures are exact obligations; no inhabitant is
asserted in the tree.

## 5. Verdict

- Actual: four canonical-lift arrows from I.fLinkAt; commutation from
  canonical_trans under the actual link-path equality.
- Not actual: the same square with paper evaluation/Kummer provenance.
- First exact missing: source evaluation arrow upperEnv + Kummer verticals
  (ThetaLinkSquareData inhabitant), not the canonical-link path equality.
- No fake upperEnv, no True placeholder, no wrapper of S1073.
