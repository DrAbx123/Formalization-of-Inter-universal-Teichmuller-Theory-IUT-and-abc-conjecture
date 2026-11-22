/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# Mzk1ThetaPilotObjectActual — O2 Theta-pilot object (real construction)

A499 object construction: the Theta-pilot object of the four-triangle route,
built from the actual source data, with NO q/(2ℓ) definition:

* `Vbad` — the finite bad locus `Bad (nativePlaceSelection T)`;
* `qroot` — the actual `2ℓ`-th root of the q-parameter: the root-extension
  element `rootNormedElement T b` with `qroot^(2ℓ) = algebraMap q`
  (`rootNormedElement_L_pow`, S1902 root construction);
* `thetaValue j = qroot^(gaussExponent j)` (the paper's `q_v^{j^2}`, for the
  signed label `j`), with the power relation `thetaValue j ^ (2ℓ) = q^(gaussExponent j)`;
* `ind1Images` — label-permutation possible images of the theta vector;
* `ind2Images` — `μ_{2ℓ}`-multiplication possible images (Kummer indeterminacy);
* `ind3Images` — unit-multiplication possible images (log-shell indeterminacy);
* `possibleImages = ind1 ∪ ind2 ∪ ind3` with the base theta vector in it;
* `hull = s1902Hull T` — the actual `λ·O` product hull of the S1902 Theta image,
  with `imageSet ⊆ hull` proved.

The object is a structure whose fields are all derived from these fixed
definitions; `thetaPilotData_constructed` records the definitional identities.
No interface, no parameter-supplied object, no incomplete proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual `2ℓ`-th root of the q-parameter at a bad place, in the root
extension `L_b = K_b(root_b)`. -/
noncomputable def qThetaRoot (b : Bad (nativePlaceSelection T)) :
    rootNormedExtension T b :=
  ⟨rootNormedElement T b, rootNormedElement_mem T b⟩

/-- The root equation `qroot^(2ℓ) = q` (q = the clause-B q_V at the place). -/
theorem qThetaRoot_pow (b : Bad (nativePlaceSelection T)) :
    (qThetaRoot T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) := by
  unfold qThetaRoot
  simpa [sourceRootQUnit] using rootNormedElement_L_pow (T := T) b

/-- The Theta value `qroot^(gaussExponent j) = q^{j^2}` of the signed label `j`,
as a section of the S1902 product carrier. -/
noncomputable def qThetaValue (j : SignedLabel l.value) : S1902Carrier T :=
  fun b => (qThetaRoot T b) ^ (gaussExponent j.1).toNat

/-- The theta value has the defining power form. -/
theorem qThetaValue_def (j : SignedLabel l.value) (b : Bad (nativePlaceSelection T)) :
    qThetaValue T j b = (qThetaRoot T b) ^ (gaussExponent j.1).toNat := rfl

/-- The `2ℓ`-th power of the theta value is the q-power `q^{gaussExponent j}`. -/
theorem qThetaValue_pow (j : SignedLabel l.value) (b : Bad (nativePlaceSelection T)) :
    (qThetaValue T j b) ^ (2 * l.value) =
      (algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b)) ^ (gaussExponent j.1).toNat := by
  rw [qThetaValue_def, ← pow_mul, mul_comm, pow_mul, qThetaRoot_pow]

/-- The base theta vector over the signed labels. -/
noncomputable def qThetaVector : SignedLabel l.value → S1902Carrier T := qThetaValue T

/-- Ind1 action: relabeling of the theta vector. -/
noncomputable def ind1Act (e : Equiv.Perm (SignedLabel l.value))
    (x : SignedLabel l.value → S1902Carrier T) :
    SignedLabel l.value → S1902Carrier T := 
  fun j => x (e j)

/-- Ind2 action: multiplication by a `μ_{2ℓ}` root in each root extension. -/
noncomputable def ind2Act
    (ζ : ∀ b, rootsOfUnity (2 * l.value) (rootNormedExtension T b))
    (x : SignedLabel l.value → S1902Carrier T) :
    SignedLabel l.value → S1902Carrier T := 
  fun j b => ((ζ b : (rootNormedExtension T b)ˣ) : rootNormedExtension T b) * x j b

/-- Ind3 action: multiplication by a unit of each root extension (log-shell
indeterminacy). -/
noncomputable def ind3Act (u : ∀ b, (rootNormedExtension T b)ˣ)
    (x : SignedLabel l.value → S1902Carrier T) :
    SignedLabel l.value → S1902Carrier T :=
  fun j b => (u b : rootNormedExtension T b) * x j b

/-- Ind1 possible images of the theta vector. -/
noncomputable def ind1Images : Set (SignedLabel l.value → S1902Carrier T) :=
  Set.range (fun e : Equiv.Perm (SignedLabel l.value) => ind1Act T e (qThetaVector T))

/-- Ind2 possible images. -/
noncomputable def ind2Images : Set (SignedLabel l.value → S1902Carrier T) :=
  Set.range (fun ζ : ∀ b, rootsOfUnity (2 * l.value) (rootNormedExtension T b) =>
    ind2Act T ζ (qThetaVector T))

/-- Ind3 possible images. -/
noncomputable def ind3Images : Set (SignedLabel l.value → S1902Carrier T) :=
  Set.range (fun u : ∀ b, (rootNormedExtension T b)ˣ =>
    ind3Act T u (qThetaVector T))

/-- All possible images (Ind1 ∪ Ind2 ∪ Ind3). -/
noncomputable def possibleThetaPilotImages :
    Set (SignedLabel l.value → S1902Carrier T) :=
  ind1Images T ∪ ind2Images T ∪ ind3Images T

/-- The base theta vector is an Ind1 possible image (identity relabeling). -/
theorem qThetaVector_mem_ind1 : qThetaVector T ∈ ind1Images T := by
  refine ⟨1, ?_⟩
  funext j
  simp [ind1Act]

/-- The base theta vector lies in the union of possible images. -/
theorem qThetaVector_mem_possible : qThetaVector T ∈ possibleThetaPilotImages T := by
  unfold possibleThetaPilotImages
  exact Or.inl (Or.inl (qThetaVector_mem_ind1 T))

/-- The Theta-pilot object: V_bad, the real `2ℓ`-th root system, the theta
values, the Ind1/2/3 possible images, and the holomorphic hull. -/
structure ThetaPilotData [Fintype (Bad (nativePlaceSelection T))] where
  Vbad : Finset (Bad (nativePlaceSelection T))
  qroot : ∀ b, rootNormedExtension T b
  qroot_pow : ∀ b, (qroot b) ^ (2 * l.value) =
    algebraMap (rootBase T b) (rootNormedExtension T b)
      ((qVFamily T b).q : rootBase T b)
  thetaValue : SignedLabel l.value → S1902Carrier T
  thetaValue_def : ∀ j b, thetaValue j b = (qroot b) ^ (gaussExponent j.1).toNat
  thetaValue_pow : ∀ j b, (thetaValue j b) ^ (2 * l.value) =
    (algebraMap (rootBase T b) (rootNormedExtension T b)
      ((qVFamily T b).q : rootBase T b)) ^ (gaussExponent j.1).toNat
  ind1Images : Set (SignedLabel l.value → S1902Carrier T)
  ind2Images : Set (SignedLabel l.value → S1902Carrier T)
  ind3Images : Set (SignedLabel l.value → S1902Carrier T)
  possibleImages : Set (SignedLabel l.value → S1902Carrier T)
  possibleImages_eq : possibleImages = ind1Images ∪ ind2Images ∪ ind3Images
  thetaVector_mem_possible : (fun j => thetaValue j) ∈ possibleImages
  imageSet : Set (S1902Carrier T)
  imageSet_eq : imageSet = s1902ImageSet T
  hull : Set (S1902Carrier T)
  hull_eq : hull = s1902Hull T
  imageSet_subset_hull : imageSet ⊆ hull

/-- The real Theta-pilot object constructed from the source data. -/
noncomputable def thetaPilotData [Fintype (Bad (nativePlaceSelection T))] :
    ThetaPilotData T where
  Vbad := Finset.univ
  qroot := qThetaRoot T
  qroot_pow := qThetaRoot_pow T
  thetaValue := qThetaValue T
  thetaValue_def := qThetaValue_def T
  thetaValue_pow := qThetaValue_pow T
  ind1Images := ind1Images T
  ind2Images := ind2Images T
  ind3Images := ind3Images T
  possibleImages := possibleThetaPilotImages T
  possibleImages_eq := rfl
  thetaVector_mem_possible := qThetaVector_mem_possible T
  imageSet := s1902ImageSet T
  imageSet_eq := rfl
  hull := s1902Hull T
  hull_eq := rfl
  imageSet_subset_hull := s1902ImageSet_subset_hull T

/-- `_constructed`: the object's fields are the fixed real definitions above. -/
theorem thetaPilotData_constructed [Fintype (Bad (nativePlaceSelection T))] :
    (thetaPilotData T).qroot = qThetaRoot T ∧
    (thetaPilotData T).thetaValue = qThetaValue T ∧
    (thetaPilotData T).ind1Images = ind1Images T ∧
    (thetaPilotData T).ind2Images = ind2Images T ∧
    (thetaPilotData T).ind3Images = ind3Images T ∧
    (thetaPilotData T).possibleImages = possibleThetaPilotImages T ∧
    (thetaPilotData T).imageSet = s1902ImageSet T ∧
    (thetaPilotData T).hull = s1902Hull T := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#check qThetaRoot_pow
#check qThetaValue_pow
#check qThetaVector_mem_possible
#check thetaPilotData_constructed

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotObjectActual
end
