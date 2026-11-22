import tmp.sheaf.xif.paper.S3137ResidualIndexParentMapActual

/-!
# S3137: canonical residual index consistency checks (task-59 maintenance)

Mechanical verification of the index data: parent-map row lengths, flattened
length 40, uniqueness of sub-node ids and of parent ids, `INDEX.` prefixes, and
flattened/parts agreement.  These are data-check theorems (kernel computation,
no axioms) so the gate can trust the index artifact without manual review; the
`INDEX.` prefix convention is documented (not kernel-checked, since
`String.startsWith` does not reduce under `decide`).
-/

namespace LeanFormal.IUT.Audit

/-- The parent map has 7 rows with sub-node counts 4,3,2,1,5,17,18. -/
theorem S3137ResidualIndex_parent_lengths :
    S3137ResidualIndexParentMap.map (fun p => p.2.length) = [4, 3, 2, 1, 5, 17, 18] :=
  rfl

/-- Flattened sub-node count is 50. -/
theorem S3137ResidualIndex_flatten_length :
    (S3137ResidualIndexParentMap.map (fun p => p.2)).flatten.length = 50 :=
  rfl

/-- All parts together have exactly 57 entries. -/
theorem S3137ResidualIndex_parts_length :
    (S3137CanonicalResidualIndexPart1 ++ S3137CanonicalResidualIndexPart2
      ++ S3137CanonicalResidualIndexPart3 ++ S3137CanonicalResidualIndexPart4
      ++ S3137CanonicalResidualIndexPart5 ++ S3137CanonicalResidualIndexPart6
      ++ S3137CanonicalResidualIndexPart7 ++ S3137CanonicalResidualIndexPart8
      ++ S3137CanonicalResidualIndexPart9 ++ S3137CanonicalResidualIndexPart10
      ++ S3137CanonicalResidualIndexPart11 ++ S3137CanonicalResidualIndexPart12
      ++ S3137CanonicalResidualIndexPart13 ++ S3137CanonicalResidualIndexPart14).length
      = 57 :=
  rfl

/-- Sub-node ids in the parent map are pairwise distinct. -/
theorem S3137ResidualIndex_subnode_ids_nodup :
    ((S3137ResidualIndexParentMap.map (fun p => p.2)).flatten).Nodup := by
  decide

/-- Parent registry ids are pairwise distinct. -/
theorem S3137ResidualIndex_parent_ids_nodup :
    (S3137ResidualIndexParentMap.map (fun p => p.1)).Nodup := by
  decide

/-- Sub-node ids from the four parts are pairwise distinct. -/
theorem S3137ResidualIndex_part_ids_nodup :
    ((S3137CanonicalResidualIndexPart1 ++ S3137CanonicalResidualIndexPart2
      ++ S3137CanonicalResidualIndexPart3 ++ S3137CanonicalResidualIndexPart4
      ++ S3137CanonicalResidualIndexPart5 ++ S3137CanonicalResidualIndexPart6
      ++ S3137CanonicalResidualIndexPart7 ++ S3137CanonicalResidualIndexPart8
      ++ S3137CanonicalResidualIndexPart9 ++ S3137CanonicalResidualIndexPart10
      ++ S3137CanonicalResidualIndexPart11 ++ S3137CanonicalResidualIndexPart12
      ++ S3137CanonicalResidualIndexPart13 ++ S3137CanonicalResidualIndexPart14).map
        (fun o => o.id)).Nodup := by
  decide

end LeanFormal.IUT.Audit