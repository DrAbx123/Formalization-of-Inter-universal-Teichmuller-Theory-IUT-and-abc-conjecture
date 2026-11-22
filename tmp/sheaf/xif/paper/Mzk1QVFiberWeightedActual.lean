import tmp.sheaf.xif.paper.Mzk1QVWeightedActual
import tmp.sheaf.xif.paper.Mzk1QVIndexMapActual
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1QVFiberWeightedActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [DecidableEq (FinitePlaceAtPrime F p)]
/-- Fiber-summed multiplicity: each bad place contributes its qV effective
multiplicity to its index i. -/
noncomputable def fiberMultWeighted
    (idx : Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime F p)
    (i : FinitePlaceAtPrime F p) : Real :=
  (Finset.univ.filter (fun b : Bad (nativePlaceSelection X.S) => idx b = i)).sum
    (fun b => (qVEffectiveMultiplicity X b : Real))
/-- Reindex bridge from F-place fiber sums to the bad-place sum.  This is the
exact missing `hmult`/fiber identity, stated as a hypothesis. -/
def MqFiberBadSumBridge
    (idx : Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime F p)
    (logBase : FinitePlaceAtPrime F p → Real) : Prop :=
  (∑ i : FinitePlaceAtPrime F p, fiberMultWeighted X idx i * logBase i) =
    ∑ b : Bad (nativePlaceSelection X.S),
      (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1)
/-- Conditional MqFiber = bad weighted sum, from the explicit fiber-multiplicity
and log-identification hypotheses plus the reindex bridge. -/
theorem MqFiber_eq_badWeighted_of_fiber
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (idx : Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime F p)
    (logBase : FinitePlaceAtPrime F p → Real)
    (hfr : ∀ i, fiberMult X b i = fiberMultWeighted X idx i)
    (hlog : ∀ i, Real.log (residueNormBase ((b i).1)) = logBase i)
    (hreindex : MqFiberBadSumBridge X idx logBase) :
    MqFiber (p := p) X b =
      ∑ b' : Bad (nativePlaceSelection X.S),
        (qVEffectiveMultiplicity X b' : Real) * Real.log (residueNormBase b'.1) := by
  unfold MqFiber
  have hsum : (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i * Real.log (residueNormBase ((b i).1))) =
      ∑ i : FinitePlaceAtPrime F p, fiberMultWeighted X idx i * logBase i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hfr i, hlog i]
  rw [hsum]
  exact hreindex

/-- The reindex bridge follows from a bad/fiber log-identification hypothesis;
no bijection is used. -/
theorem MqFiberBadSumBridge_of_logBridge
    (idx : Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime F p)
    (logBase : FinitePlaceAtPrime F p → Real)
    (hlog : ∀ b : Bad (nativePlaceSelection X.S),
      Real.log (residueNormBase b.1) = logBase (idx b)) :
    MqFiberBadSumBridge X idx logBase := by
  unfold MqFiberBadSumBridge fiberMultWeighted
  have h1 : ∀ i : FinitePlaceAtPrime F p,
      (Finset.univ.filter (fun b : Bad (nativePlaceSelection X.S) => idx b = i)).sum
        (fun b => (qVEffectiveMultiplicity X b : Real)) * logBase i =
      (Finset.univ.filter (fun b : Bad (nativePlaceSelection X.S) => idx b = i)).sum
        (fun b => (qVEffectiveMultiplicity X b : Real) * logBase (idx b)) := by
    intro i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [hb.2]
  simp_rw [h1]
  rw [Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Bad (nativePlaceSelection X.S))))
    (t := (Finset.univ : Finset (FinitePlaceAtPrime F p))) (g := idx)
    (h := by intro b _; simp)
    (f := fun b => (qVEffectiveMultiplicity X b : Real) * logBase (idx b))]
  apply Finset.sum_congr rfl
  intro b _
  rw [← hlog b]
#check MqFiberBadSumBridge_of_logBridge


/-- Fiber consistency: if `b` is a section of `idx` with singleton fibers, then
the single-point multiplicity is the fiber sum. -/
theorem fiberMult_eq_fiberMultWeighted_of_section
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (idx : Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime F p)
    (hsec : ∀ i : FinitePlaceAtPrime F p, idx (b i) = i)
    (huniq : ∀ (i : FinitePlaceAtPrime F p) (b' : Bad (nativePlaceSelection X.S)),
      idx b' = i → b' = b i) :
    ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i = fiberMultWeighted X idx i := by
  intro i
  change (qVEffectiveMultiplicity X (b i) : Real) = fiberMultWeighted X idx i
  unfold fiberMultWeighted
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single (b i)]
  · simp [hsec i]
  · intro b' _ hb'
    by_cases h : idx b' = i
    · exact (hb' (huniq i b' h)).elim
    · simp [h]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim
#check fiberMult_eq_fiberMultWeighted_of_section



#check fiberMultWeighted
#check MqFiberBadSumBridge
#check MqFiber_eq_badWeighted_of_fiber
end LeanFormal.IUT.XiFPaper.Mzk1QVFiberWeightedActual
end