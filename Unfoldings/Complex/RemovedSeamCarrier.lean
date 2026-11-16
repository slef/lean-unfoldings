module

public import Unfoldings.Complex.PhysicalCutEquiv
public import Unfoldings.Complex.RegularSeamUnique

/-! Removing original edge pairings is exactly cutting their literal spatial segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

/-- The literal closed spatial carrier of the removed original seams. -/
def removedSeamCarrier (retain : Set C.Seam) : Set Space :=
  ⋃ s : {s : C.Seam // s ∉ retain},
    F.place (C.left s.val).face '' (C.triangle (C.left s.val).face).edge (C.left s.val).edge

theorem removed_edge_mem_removedSeamCarrier (retain : Set C.Seam) (s : C.Seam)
    (removed : s ∉ retain) (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    F.place (C.left s).face x.val ∈ F.removedSeamCarrier retain :=
  Set.mem_iUnion.mpr ⟨⟨s, removed⟩, x.val, x.property, rfl⟩

/-- The finite original cut carrier is closed, including all of its endpoints. -/
theorem isClosed_removedSeamCarrier (retain : Set C.Seam) :
    IsClosed (F.removedSeamCarrier retain) :=
  isClosed_iUnion_of_finite fun s =>
    (((C.triangle (C.left s.val).face).compact_edge (C.left s.val).edge).image
      (F.place (C.left s.val).face).continuous).isClosed

/-- Embedded original triangles cannot have a retained open edge cross a removed seam,
including at a vertex of the removed seam. -/
theorem openSeamImage_disjoint_removedSeamCarrier (embedded : F.IsEmbedded)
    (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain) :
    Disjoint (F.openSeamImage s) (F.removedSeamCarrier retain) := by
  apply Set.disjoint_left.mpr
  intro z on_open on_removed
  let f := (C.left s).face
  let e := (C.left s).edge
  have image : F.place f '' openSegment ℝ ((C.triangle f).vertex e)
      ((C.triangle f).vertex (Triangle.next e)) = F.openSeamImage s :=
    image_openSegment ℝ (F.place f).toAffineMap _ _
  obtain ⟨p, inside, placed⟩ := Eq.mpr
    (congrArg (fun a : Set Space => z ∈ a) image) on_open
  let x : (C.triangle f).Edge e :=
    ⟨p, openSegment_subset_segment ℝ _ _ inside⟩
  have regular : ¬ C.IsVertex (C.edgePoint (C.left s) x) := by
    intro vertex
    rcases ((C.triangle f).edge_vertex_iff e x).mp vertex with first | last
    · have endpoint := Eq.mp
        (congrArg (fun q : Plane => q ∈ openSegment ℝ ((C.triangle f).vertex e)
          ((C.triangle f).vertex (Triangle.next e))) first) inside
      exact (C.triangle f).edge_endpoints_ne e (left_mem_openSegment_iff.mp endpoint)
    · have endpoint := Eq.mp
        (congrArg (fun q : Plane => q ∈ openSegment ℝ ((C.triangle f).vertex e)
          ((C.triangle f).vertex (Triangle.next e))) last) inside
      exact (C.triangle f).edge_endpoints_ne e (right_mem_openSegment_iff.mp endpoint)
  obtain ⟨t, on_edge⟩ := Set.mem_iUnion.mp on_removed
  obtain ⟨q, hq, equal⟩ := on_edge
  let y : (C.triangle (C.left t.val).face).Edge (C.left t.val).edge := ⟨q, hq⟩
  have related := F.isEmbedded_iff.mp embedded (C.edgePoint (C.left s) x)
    (C.edgePoint (C.left t.val) y) (placed.trans equal.symm)
  exact t.property ((C.seams_eq_of_related_regular_edgePoints s t.val x y regular related) ▸ kept)

/-- For an embedded folding, deleting any chosen original pairings constructs exactly the
physical cut along the removed spatial edges, with all original corner classes intact. -/
def removedSeamCutEquiv (embedded : F.IsEmbedded) (retain : Set C.Seam) :
    C.Realization retain ≃ᵢ F.PhysicalCut (F.removedSeamCarrier retain) :=
  F.complexPhysicalCutEquiv embedded retain (F.removedSeamCarrier retain)
    (F.removed_edge_mem_removedSeamCarrier retain)
    (F.openSeamImage_disjoint_removedSeamCarrier embedded retain)

@[simp] theorem removedSeamCutEquiv_faceMap (embedded : F.IsEmbedded)
    (retain : Set C.Seam) (f : Face) (x : C.Cell f) :
    F.removedSeamCutEquiv embedded retain (C.faceMap retain f x) =
      F.faceMapToPhysicalCut (F.removedSeamCarrier retain) f x := rfl

theorem fold_removedSeamCutEquiv (embedded : F.IsEmbedded)
    (retain : Set C.Seam) (x : C.Realization retain) :
    (F.physicalCutSeams (F.removedSeamCarrier retain)).fold
      (F.removedSeamCutEquiv embedded retain x) = F.toSpace retain x :=
  F.fold_complexPhysicalCutEquiv embedded retain (F.removedSeamCarrier retain)
    (F.removed_edge_mem_removedSeamCarrier retain)
    (F.openSeamImage_disjoint_removedSeamCarrier embedded retain) x

end Unfoldings.SpatialFolding
