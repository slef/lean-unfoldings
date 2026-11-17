module

public import Unfoldings.Complex.Neighborhood
public import Unfoldings.Complex.Folding
public import Unfoldings.Boundary.Exact

/-! The two original cut banks exhaust every regular fiber of an embedded removed edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (embedded : F.IsEmbedded) (retain : Set C.Seam)

include embedded in
/-- Every actual metric copy over a nonvertex point of a removed original edge is
one of its two named original bank copies. No local fan or fiber certificate is supplied. -/
theorem eq_leftBank_or_rightBank_of_regular_position (s : C.Seam) (removed : s ∉ retain)
    (q : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex q.val)
    (x : C.Realization retain)
    (position : F.toSpace retain x = F.place (C.left s).face q.val) :
    x = C.bankMap retain (C.leftBank retain s removed) q ∨
      x = C.bankMap retain (C.rightBank retain s removed) (C.identify s q) := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  let first := C.edgePoint (C.left s) q
  let last := C.edgePoint (C.right s) (C.identify s q)
  have full : MetricGluing.point C.Cell (C.glue Set.univ) first =
      MetricGluing.point C.Cell (C.glue Set.univ) a := by
    apply embedded
    change F.toSpace Set.univ
      (C.faceMap Set.univ (C.left s).face
        ((C.triangle (C.left s).face).edgeMap (C.left s).edge q)) =
        F.toSpace Set.univ (C.faceMap Set.univ a.1 a.2)
    rw [F.toSpace_faceMap, F.toSpace_faceMap]
    change F.place (C.left s).face q.val = F.toSpace retain (C.faceMap retain a.1 a.2)
    rw [F.toSpace_faceMap]
    exact position.symm
  have crossing : C.Crosses Set.univ first last :=
    (C.crosses_iff Set.univ first last).mpr (Or.inl ⟨s, Set.mem_univ _, q, rfl, rfl⟩)
  have regular_first : ¬ C.IsVertex first := regular
  rcases (C.eqvGen_iff_eq_or_neighbor regular_first crossing).mp
      ((C.point_eq_iff Set.univ first a).mp full) with first_copy | last_copy
  · exact Or.inl (congrArg (MetricGluing.point C.Cell (C.glue retain)) first_copy)
  · exact Or.inr (congrArg (MetricGluing.point C.Cell (C.glue retain)) last_copy)

end Unfoldings.SpatialFolding
