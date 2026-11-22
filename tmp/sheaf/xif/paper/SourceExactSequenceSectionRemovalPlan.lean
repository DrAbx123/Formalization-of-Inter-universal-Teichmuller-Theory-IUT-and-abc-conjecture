import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# SourceExactSequenceClause.sectionMap: obstruction and minimal removal plan

Question: can SourceExactSequenceClause.sectionMap be constructed from the
actual cusp / cuspidal decomposition group data?

Answer: no.

The actual cuspidal data are

  OrbicurveCuspidalDecompositionData groups
    cusp : OrbicurveBoundaryCusp X
    decompositionSubgroup : ClosedSubgroup groups.arithmetic.group
    decompositionProjection_surjective :
      Function.Surjective (profiniteClosedSubgroupRestriction ...)

and the derived exact sequence

  inertia -> decomposition -> galois.

These data give a surjective projection decomposition -> galois and its kernel
inertia.  They do NOT give a group homomorphism galois -> decomposition (or
galois -> arithmetic) whose composite with the projection is the identity.
OrbicurveBoundaryCusp itself carries only compactification/open map/residue
point/boundary condition; it carries no decomposition subgroup and no splitting.
A set-theoretic choice of preimages is not a MonoidHom and cannot inhabit
SourceExactSequenceClause.sectionMap.

The reduced target contract therefore must drop the section fields.  Minimal
refactor list:

1. SourceExactSequenceClause (SourceDefinition31Boundary.lean, lines 321-335):
   remove
     sectionMap : baseGroup ->* coverGroup
     section_right_inverse : forall x, projection (sectionMap x) = x
   Keep baseGroup/coverGroup/geometricGroup, injection, projection,
   injection_injective, projection_surjective, exact_at_cover.

2. SourceExactSequenceClause namespace (same file, lines 341-450):
   delete section-dependent theorems:
     section_right_inverse_spec, section_map_one, section_map_mul,
     section_map_inv, section_map_eq, section_injective,
     projection_section_*, section_cancel, and any theorem whose statement
     mentions E.sectionMap.
   Keep projection/injection/exactness lemmas.

3. SourceOrbicurveClause (same file, around lines 455-515):
   delete the section_right_inverse wrapper using C.exactSequence.sectionMap.

4. SourceDefinition31RootLemmas.lean:
   delete or move behind an explicit splitting hypothesis the blocks using
   S.orbicurve.exactSequence.sectionMap:
     SourceExactSequenceClause.rootSplitLift/rootResidual/rootKernelCoordinate/
       rootCanonical_decomposition/rootKernel_closed_*/rootProjection_section_*/
       rootConjugateLift/rootAction_* (lines 34-272);
     definition31_exact_sequence_section_* (lines 632-678);
     definition31_orbicurve_exact_section (line 1231);
     stage_d6_section_* (lines 2768-2894).
   The non-section statements (injection/projection/exactness/root kernel
   decomposition without lifted section) stay.

5. SourceOriginalInput.lean (line 1413):
   delete initial_orbicurve_exact_section (or reformulate with a supplied
   splitting).

6. Constructors/producers that currently take a splitting:
   SourceClauseConstructors.exactSequenceOfFundamentalGroup;
   SourceDefinition31OrbicurveInstance exact-sequence assembly;
   NativeSourceOrbicurveActual.sourceExactSequenceOfGroups;
   NativeAssemblyCurveFieldsActual.nativeExactSequence.
   Remove their sectionMap argument and section_right_inverse proof field.

7. ExactSequenceSplittingActual.lean:
   this file exists only to provide the splitting; delete it from the target
   closure or turn it into an optional theorem not consumed by
   SourceDefinition31Data.

8. Other consumers found by
     exactSequence.sectionMap / exactSequence.section_right_inverse
   are only the RootLemmas/SourceOriginalInput sites above; conditional
   assembly files may retain an explicit splitting hypothesis if their theorem
   statement is about split data, but the source contract itself must not
   require it.

After these edits, the Definition 3.1 orbicurve contract remains the actual
short exact sequence

  1 -> geometric -> cover -> base -> 1

with exactness, without asserting a splitting that the cusp/decomposition data
do not supply.
-/

#check Iut.OrbicurveCuspidalDecompositionData
#check Iut.OrbicurveCuspidalDecompositionData.exactSequence
#check Iut.OrbicurveCuspidalDecompositionData.ambientEmbedding
#check Iut.OrbicurveBoundaryCusp

end
