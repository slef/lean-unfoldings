module

public import Unfoldings.Roof.Basic
public import Unfoldings.Complex.RemovedSeamCarrier

/-! Original removed seams give closed projected cut carriers without losing their metric copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

/-- A finite union of removed original spatial edges is compact. -/
theorem isCompact_removedSeamCarrier (retain : Set C.Seam) :
    IsCompact (F.removedSeamCarrier retain) :=
  isCompact_iUnion fun s => ((C.triangle (C.left s.val).face).compact_edge
    (C.left s.val).edge).image (F.place (C.left s.val).face).continuous

/-- Every removed edge lies on the original physical surface. -/
theorem removedSeamCarrier_subset_surface (retain : Set C.Seam) :
    F.removedSeamCarrier retain ⊆ F.surface := by
  rintro z member
  obtain ⟨s, p, on_edge, rfl⟩ := Set.mem_iUnion.mp member
  exact Set.mem_iUnion.mpr ⟨(C.left s.val).face, p,
    (C.triangle (C.left s.val).face).edge_subset _ on_edge, rfl⟩

/-- The actual open original seam also lies on the original physical surface. -/
theorem openSeamImage_subset_surface (s : C.Seam) : F.openSeamImage s ⊆ F.surface := by
  have image := image_openSegment ℝ (F.place (C.left s).face).toAffineMap
    ((C.triangle (C.left s).face).vertex (C.left s).edge)
    ((C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge))
  intro z member
  obtain ⟨p, on_edge, rfl⟩ := image.symm.subset member
  exact Set.mem_iUnion.mpr ⟨(C.left s).face, p,
    (C.triangle (C.left s).face).edge_subset _
      (openSegment_subset_segment ℝ _ _ on_edge), rfl⟩

end Unfoldings.SpatialFolding

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Vertical projection identifies original physical surface points uniquely. -/
theorem horizontal_injOn_surface : Set.InjOn Cap.horizontal K.folding.surface := by
  intro x on_x y on_y same
  obtain ⟨a, at_a⟩ := K.folding.range_toSpace Set.univ |>.symm.subset on_x
  obtain ⟨b, at_b⟩ := K.folding.range_toSpace Set.univ |>.symm.subset on_y
  have equal := K.projection_injective
    ((congrArg Cap.horizontal at_a).trans (same.trans (congrArg Cap.horizontal at_b).symm))
  exact at_a.symm.trans ((congrArg (K.folding.toSpace Set.univ) equal).trans at_b)

/-- The exact horizontal carrier of any chosen removed original seams. -/
def removedProjectedSeamCarrier (retain : Set C.Seam) : Set Plane :=
  Cap.horizontal '' K.folding.removedSeamCarrier retain

theorem isClosed_removedProjectedSeamCarrier (retain : Set C.Seam) :
    IsClosed (K.removedProjectedSeamCarrier retain) :=
  ((K.folding.isCompact_removedSeamCarrier retain).image Cap.horizontalCLM.continuous).isClosed

/-- With no seams removed the actual carrier is empty. -/
@[simp] theorem removedProjectedSeamCarrier_univ :
    K.removedProjectedSeamCarrier Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p member
  obtain ⟨z, removed, _⟩ := member
  obtain ⟨s, _⟩ := Set.mem_iUnion.mp removed
  exact s.property (Set.mem_univ _)

/-- Removing more original seams only adds to their actual projected carrier. -/
theorem removedProjectedSeamCarrier_antitone {first last : Set C.Seam} (more : last ⊆ first) :
    K.removedProjectedSeamCarrier first ⊆ K.removedProjectedSeamCarrier last := by
  rintro p ⟨z, removed, rfl⟩
  obtain ⟨s, point, member, rfl⟩ := Set.mem_iUnion.mp removed
  exact ⟨_, Set.mem_iUnion.mpr
    ⟨⟨s.val, fun kept => s.property (more kept)⟩, point, member, rfl⟩, rfl⟩

/-- Original spatial cut membership is exactly recovered from projection on the whole surface. -/
theorem mem_removedSeamCarrier_iff_projected (retain : Set C.Seam) {z : Space}
    (on_surface : z ∈ K.folding.surface) :
    z ∈ K.folding.removedSeamCarrier retain ↔
      Cap.horizontal z ∈ K.removedProjectedSeamCarrier retain := by
  constructor
  · intro member
    exact ⟨z, member, rfl⟩
  · rintro ⟨w, removed, same⟩
    have equal := K.horizontal_injOn_surface
      (K.folding.removedSeamCarrier_subset_surface retain removed) on_surface same
    exact equal ▸ removed

/-- No retained open original seam meets the projected carrier of the removed seams. -/
theorem openSeamImage_disjoint_projected_removed (retain : Set C.Seam)
    (s : C.Seam) (kept : s ∈ retain) :
    Disjoint (K.folding.openSeamImage s)
      (Cap.horizontal ⁻¹' K.removedProjectedSeamCarrier retain) :=
  Set.disjoint_left.mpr (fun _z on_open on_cut =>
    Set.disjoint_left.mp
      (K.folding.openSeamImage_disjoint_removedSeamCarrier K.embedded retain s kept) on_open
      ((K.mem_removedSeamCarrier_iff_projected retain
        (K.folding.openSeamImage_subset_surface s on_open)).mpr on_cut))

/-- Every removed closed original edge remains in that exact projected physical cut. -/
theorem removed_edge_mem_projected_removed (retain : Set C.Seam) (s : C.Seam)
    (removed : s ∉ retain) (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    Cap.horizontal (K.folding.place (C.left s).face x.val) ∈ K.removedProjectedSeamCarrier retain :=
  ⟨_, K.folding.removed_edge_mem_removedSeamCarrier retain s removed x, rfl⟩

/-- Any intermediate original retained-seam complex has exactly this projected physical cut
metric, with its original endpoint copies and face tags intact. -/
def projectedRemovedSeamCutEquiv (retain : Set C.Seam) :
    C.Realization retain ≃ᵢ
      K.folding.PhysicalCut (Cap.horizontal ⁻¹' K.removedProjectedSeamCarrier retain) :=
  K.folding.complexPhysicalCutEquiv K.embedded retain
    (Cap.horizontal ⁻¹' K.removedProjectedSeamCarrier retain)
    (K.removed_edge_mem_projected_removed retain)
    (K.openSeamImage_disjoint_projected_removed retain)

end Unfoldings.ConvexRoof
