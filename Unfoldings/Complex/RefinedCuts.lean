module

public import Unfoldings.Complex.SubdivisionComposition
public import Unfoldings.Complex.SubdivisionFolding
public import Unfoldings.Polyhedron.CutDiskIff

/-!
# Cuts carried by a conforming refinement

A refined seam can cross an original face. Cutting such seams uses the fine
complex's constructed route metric; its projection to the old surface is
nonexpanding. Compatible further refinement gives the same cut metric.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision.Conforming

universe u v w z a b

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {Grandchild : Type a} [Fintype Grandchild]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {E : TriangleComplex.{a, b} Grandchild} {S : C.Subdivision D}
  (H : S.Conforming Set.univ Set.univ)

/-- Restore the refined cuts and identify the refined uncut surface with the original one. -/
def cutProjection (retain : Set D.Seam) : D.Realization retain → C.Realization Set.univ :=
  fun x => H.metricEquiv (D.forgetCuts (Set.subset_univ retain) x)

@[simp] theorem cutProjection_faceMap (retain : Set D.Seam) (g : Child) (x : D.Cell g) :
    H.cutProjection retain (D.faceMap retain g x) =
      C.faceMap Set.univ (S.parent g) (S.parentCell g x) := rfl

theorem cutProjection_lipschitz (retain : Set D.Seam) :
    LipschitzWith 1 (H.cutProjection retain) := by
  intro x y
  change edist (H.metricEquiv _) (H.metricEquiv _) ≤ _
  rw [H.metricEquiv.isometry.edist_eq]
  exact (D.forgetCuts_lipschitz (Set.subset_univ retain)).edist_le_mul x y

theorem cutProjection_surjective (retain : Set D.Seam) :
    Function.Surjective (H.cutProjection retain) :=
  H.metricEquiv.surjective.comp (D.forgetCuts_surjective (Set.subset_univ retain))

/-- Refining a cut presentation preserves both the cut metric and its surface projection. -/
theorem cutProjection_comp {T : D.Subdivision E} (K : T.Conforming Set.univ Set.univ)
    {retain : Set D.Seam} {fineRetain : Set E.Seam} (L : T.Conforming retain fineRetain)
    (x : E.Realization fineRetain) :
    H.cutProjection retain (L.metricEquiv x) = (H.comp K).cutProjection fineRetain x := by
  obtain ⟨⟨g, y⟩, rfl⟩ := MetricGluing.point_surjective E.Cell (E.glue fineRetain) x
  rfl

end Unfoldings.TriangleComplex.Subdivision.Conforming

namespace Unfoldings.SpatialFolding

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  (F : SpatialFolding C) (S : C.Subdivision D) (H : S.Conforming Set.univ Set.univ)

/-- Each projected boundary bank is an actual spatial straight segment. -/
theorem bankBoundary_image (retain : Set C.Seam) :
    F.toSpace retain '' C.bankBoundary retain =
      ⋃ bank : C.BoundaryBank retain,
        segment ℝ (F.place bank.val.face ((C.triangle bank.val.face).vertex bank.val.edge))
          (F.place bank.val.face ((C.triangle bank.val.face).vertex
            (Triangle.next bank.val.edge))) := by
  ext z
  constructor
  · rintro ⟨p, boundary, rfl⟩
    obtain ⟨bank, x, rfl⟩ := Set.mem_iUnion.mp boundary
    apply Set.mem_iUnion.mpr
    refine ⟨bank, ?_⟩
    exact (image_segment ℝ (F.place bank.val.face).toAffineMap _ _).subset
      ⟨x.val, x.property, rfl⟩
  · intro member
    obtain ⟨bank, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨x, hx, rfl⟩ :=
      (image_segment ℝ (F.place bank.val.face).toAffineMap _ _).symm.subset member
    exact ⟨C.bankMap retain bank ⟨x, hx⟩,
      C.bankMap_mem_bankBoundary retain bank ⟨x, hx⟩, rfl⟩

theorem subdivide_cutProjection (retain : Set D.Seam) (x : D.Realization retain) :
    F.toSpace Set.univ (H.cutProjection retain x) = (F.subdivide S H).toSpace retain x := by
  obtain ⟨⟨g, y⟩, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue retain) x
  rfl

include S H in
/-- The sphere cut-tree criterion applies to cuts inside original faces via their refinement. -/
theorem ConvexBoundary.refinedCutDisk_iff_tree (P : F.ConvexBoundary) (retain : Set D.Seam) :
    Nonempty (D.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) ↔
      (D.cutSeamGraph retain).IsTree :=
  (SpatialFolding.ConvexBoundary.subdivide F S H P).cutDisk_iff_cutSeamGraph_tree retain

end Unfoldings.SpatialFolding
