module

public import Unfoldings.Source.Bisectors

/-!
# Closed finite supports for the source cut locus

Add the three edge supporting lines of each original face to the genuine
virtual-source bisectors. The resulting face sets are closed, so their compact
surface images contain the closure of all nonunique endpoints, including cone
leaves. In a face interior, exact tagged-point uniqueness removes every other
face from this cover.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

theorem exists_coord_eq_zero_of_not_interior (T : Triangle) {x : Plane}
    (member : x ∈ T.carrier) (outside : x ∉ interior T.carrier) :
    ∃ i, T.coord i x = 0 := by
  have nonnegative : ∀ i, 0 ≤ T.coord i x := by
    rwa [T.carrier_eq_nonneg_coord] at member
  have not_positive : ¬ ∀ i, 0 < T.coord i x := by
    simpa only [T.interior_eq_pos_coord, Set.mem_ofPred_eq] using outside
  obtain ⟨i, hi⟩ := not_forall.mp not_positive
  exact ⟨i, le_antisymm (le_of_not_gt hi) (nonnegative i)⟩

end Unfoldings.Triangle

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceFaceCutSupport :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      C.PointFiber Set.univ source → Face → Set Plane := by
  let := P.metricSpace
  intro source R base f
  exact P.sourceBisectors R base ∪ ⋃ i : Fin 3, {x | (C.triangle f).coord i x = 0}

theorem isClosed_sourceFaceCutSupport :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (f : Face),
      IsClosed (P.sourceFaceCutSupport R base f) := by
  let := P.metricSpace
  intro source R base f
  exact (P.isClosed_sourceBisectors R base).union
    (isClosed_iUnion_of_finite (fun i =>
      isClosed_eq ((C.triangle f).continuous_coord i) continuous_const))

theorem sourceCutLocus_subset_face_support_images :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source),
      sourceCutLocus source ⊆ ⋃ f : Face, C.faceMap Set.univ f ''
        {x : C.Cell f | x.val ∈ P.sourceFaceCutSupport R base f} := by
  let := P.metricSpace
  intro source R base
  have closed_face (f : Face) : IsClosed (C.faceMap Set.univ f ''
      {x : C.Cell f | x.val ∈ P.sourceFaceCutSupport R base f}) :=
    (((P.isClosed_sourceFaceCutSupport R base f).preimage
      continuous_subtype_val).isCompact.image (C.faceMap_lipschitz Set.univ f).continuous).isClosed
  apply closure_minimal _ (isClosed_iUnion_of_finite closed_face)
  intro y nonunique
  obtain ⟨⟨f, x⟩, equal⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) y
  have image : C.faceMap Set.univ f x = y := equal
  refine Set.mem_iUnion.mpr ⟨f, x, ?_, image⟩
  by_cases inside : x.val ∈ interior (C.triangle f).carrier
  · exact Or.inl (P.nonunique_face_interior_mem_sourceBisectors R base f x inside
      (image.symm ▸ nonunique))
  · obtain ⟨i, zero⟩ := (C.triangle f).exists_coord_eq_zero_of_not_interior x.property inside
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, zero⟩)

theorem cut_face_interior_mem_sourceBisectors :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (f : Face) (x : C.Cell f),
      x.val ∈ interior (C.triangle f).carrier →
      C.faceMap Set.univ f x ∈ sourceCutLocus source → x.val ∈ P.sourceBisectors R base := by
  let := P.metricSpace
  intro source R base f x inside cut
  obtain ⟨g, member⟩ := Set.mem_iUnion.mp
    (P.sourceCutLocus_subset_face_support_images R base cut)
  obtain ⟨y, support, equal⟩ := member
  have tags := C.faceInterior_tag_eq Set.univ f x inside ⟨g, y⟩ equal.symm
  have same := Sigma.mk.inj_iff.mp tags
  obtain rfl := same.1
  have points : x = y := eq_of_heq (Sigma.mk.inj tags).2
  rw [← points] at support
  rcases support with bisector | edge
  · exact bisector
  · obtain ⟨i, zero⟩ := Set.mem_iUnion.mp edge
    have positive : ∀ i, 0 < (C.triangle f).coord i x.val := by
      simpa only [(C.triangle f).interior_eq_pos_coord, Set.mem_ofPred_eq] using inside
    exact ((positive i).ne' zero).elim

end Unfoldings.SpatialFolding.ConvexBoundary
