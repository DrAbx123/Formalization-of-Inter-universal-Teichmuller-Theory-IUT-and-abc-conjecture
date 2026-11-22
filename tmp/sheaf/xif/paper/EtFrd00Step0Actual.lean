/-!
# EtFrd00: STEP 0 deep-search record — EtTh / Frobenioid batch (policy §7.10; data only)

Queries: EtaleTheta|étale theta|Frobenioid|FrdI|FrdII|divisor theory|model Frobenioid|Frobenius action
Hits: LeanFormal 754 / Iut 546 / cft-port 2 / tmp/sheaf/xif/paper 2057 /
archive 17 / gap 4 / vendor 383 / corpus 160.
Corpus texts present (papers/motizuki_corpus/text):
* The Etale Theta Function and its Frobenioid-theoretic Manifestations.txt
  (+ comments / related expositions);
* The Geometry of Frobenioids I.txt, The Geometry of Frobenioids II.txt (+ comments);
* Responses to questions on Frobenioids.txt.
Anchors: [EtTh] Prop 1.1 l.784, Lemma 1.2 l.1147, Prop 1.3 l.1169, Prop 1.4 l.1338,
Prop 1.5 l.1401, Thm 1.6 l.1514, Prop 1.8 l.1761, Thm 1.10 l.1979, Prop 3.2 l.5422,
Prop 3.4 l.5657; [FrdI] Props 1.4-1.11 l.1109-1599; [FrdII] Thm 1.2 l.376,
Prop 1.5 l.584, Thm 2.4 l.818, Prop 3.4 l.1446.
Reuse decisions (no re-proof):
* theta quotient layer -> LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean (A; proved).
* concrete Frobenioid boundary -> LeanFormal/IUT/IUTII/Frobenioid/
  ConcreteSourceFrobenioidBridge.lean (A; concreteSourceFrobenioidBoundary + boundary laws).
* model Frobenioid presentation -> Iut.Foundations.SourceModelFrobenioidPresentation
  (+ RationalNaturality/ZeroEvaluation) (A; importable).
* Frobenius action assets -> Example36FrobeniusValueAction / LogShellFrobeniusAction /
  PrimeStripDivisorFrobenius / FrobenioidTransport / DivisorialMonoidMinimalReplacement (A/B).
* theta packet / SourceDefinition31Data -> reuse; canonical rooted Q_C/H_C ->
  S3131/S3132 files; H6 -> GenEll10H6ClosureActual (interface-level); A35 ->
  Indet01-03; C3 -> S3139C3ConventionClosureActual.
* Deep [EtTh] theta results -> NAMED class-B D-inputs (EtTh02DeepInputsActual,
  proved := false); [FrdI]/[FrdII] category-theoreticity theorems class B.
Pins: registry frozen 14041; no intermediate reopen.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.EtFrd00Step0Actual

/-- STEP 0 record: (query, hits, reuse/adapt decision). -/
def etFrdStep0Record : List (String × String × String) :=
  [ ("EtaleTheta|étale theta|Frobenioid|FrdI|FrdII|divisor theory|model Frobenioid|Frobenius action",
      "LeanFormal 754 / Iut 546 / paper 2057 / vendor 383 / corpus 160",
      "reuse: EtaleThetaQuotient; ConcreteSourceFrobenioidBridge; Iut.Foundations.SourceModelFrobenioid*; Example36* assets"),
    ("[EtTh] corpus", "Prop 1.1 l.784 ... Thm 1.10 l.1979; Prop 3.2/3.4 l.5422/5657",
      "statement layer EtTh01; deep inputs EtTh02 (proved := false)"),
    ("[FrdI]/[FrdII] corpus", "FrdI Props 1.4-1.11; FrdII Thm 1.2/2.4, Prop 3.4",
      "statement layer Frd01; reuse audit Frd02"),
    ("theta/frobenioid tree assets", "EtaleThetaQuotient; ConcreteSourceEtaleThetaBridge:44; ConcreteSourceFrobenioidBoundary",
      "reuse (class A); no re-proof") ]

end LeanFormal.IUT.XiFPaper.EtFrd00Step0Actual
