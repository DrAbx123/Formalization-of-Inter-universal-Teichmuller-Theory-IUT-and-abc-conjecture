/-
N8 group 3 -- S1: generator landing in the canonical arithmetic region.

Source: tmp/sheaf/n8/group3-STAGE1.md §7, minimal statement S1 (gaps G3.1,
G3.3 in §5 delimit what this does *not* assume).  Paper anchor: IUT III,
Corollary 3.12 and the q/Theta-pilot log-volume passage III:10843--10898;
distilled-02 §D requires the *actual* iota_S(x) in R(S), not merely a
same-typed x' in R(S).

The declaration below is exactly S1 as fixed in the stage-1 record, with all
binder implicit arguments.  Its consumer is the DAG node
n8-group3-q-theta-pilot (child G3.a): it is the generator-level form of the
missing source -> arithmetic arrow (G3.1), and, unlike the full-hull cover, it is
untouched by the F2 no-go of G3.3.

Proof route fixed in group3-STAGE1.md §7, implemented below:
1. I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j puts the actual
   source theta-pilot generator into the source holomorphic hull;
2. B.hull_cover writes that point as B.toSource a for a unit a whose
   underlying arithmetic element lies in the canonical hull;
3. B.theta_compat (n, j) together with injectivity of B.toSource identifies
   B.thetaLift (n, j) with a;
4. rewriting the goal by that equality leaves exactly the hull membership of 2.

All proof dependencies are inside the Project import closure (the bridge module,
SourceImageHull, FinitePlaceArithmeticTensorBlocks,
FinitePlaceArithmeticTupleCanonicalHull), so no orphan module is used and no
named sorry is needed (the §7 route is complete; SORRY-POLICY not triggered).

Standalone trial file: no production edit, not imported by Project.
-/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceArithmeticThetaPilotBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Group3

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui uK vι wV

/-- **S1.**  The arithmetic unit attached by the bridge to the source theta-pilot
generator (n, j) underlies an element of the canonical arithmetic hull
arithmeticTupleCanonicalHull places tuple.

Hypotheses are exactly the stage-1 record: the bridge B (which contains the
hull cover as a field) and injectivity of its comparison map B.toSource.  The
conclusion is not a bridge field: it is derived from hull_cover and
theta_compat, and is the generator-level statement that survives the F2
no-go (G3.3). -/
theorem ArithmeticThetaPilotBridge.thetaLift_mem_canonicalHull
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (B : ArithmeticThetaPilotBridge places tuple I v R n)
    (hinj : Function.Injective B.toSource)
    (j : SignedLabel l.value) :
    (B.thetaLift (n, j) : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleCanonicalHull places tuple := by
  -- Step 1: the actual source generator lies in the source holomorphic hull.
  have hgen : I.sourceThetaPilotPoint v R n j ∈ I.sourceHolomorphicHull v R n :=
    I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j
  -- Step 2: the bridge's hull cover exhibits an arithmetic unit over it.
  obtain ⟨a, ha, hax⟩ := B.hull_cover hgen
  -- Step 3: theta compatibility plus injectivity identify the theta lift with a.
  have h : B.toSource (B.thetaLift (n, j)) = B.toSource a :=
    (B.theta_compat (n, j)).trans hax.symm
  have heq : B.thetaLift (n, j) = a := hinj h
  -- Step 4: rewrite to the canonical-hull membership of the exhibited unit.
  rw [heq]
  exact ha

end LeanFormal.IUT.N8Group3
