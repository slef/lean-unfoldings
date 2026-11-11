module

public import Unfoldings.Cap.ExtendedCutMesh
public import Unfoldings.Cap.ParentRadialGrowth
public import Unfoldings.Geometry.LocalRadialGrowth

/-! Local outward progress on the constructed original cuts and radial skirt continuations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- A skirt component has outward progress at every point away from the outer rim. -/
theorem extended_growth_on_skirt (F : K.SkirtTailFamily Z (K.projectedVertex origin))
    {p : Plane} (member : p ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (inside : p ∈ interior (K.clipFootprint Z)) :
    LocalRadialGrowth (M.extendedGeometricCuts F) (K.projectedVertex origin) p := by
  obtain ⟨c, on_tail⟩ := Set.mem_iUnion.mp member
  have not_tip : p ≠ (F.componentTail c).tip := by
    intro equal
    exact (F.componentTail c).boundary.2 (equal ▸ inside)
  exact ((F.componentTail c).local_growth_of_not_tip on_tail not_tip).mono
    (fun _ on_component => Or.inr (Set.mem_iUnion.mpr ⟨c, on_component⟩))

/-- At an original nonroot vertex the selected original edge supplies local progress. -/
theorem extended_growth_at_nonroot (positive : 0 < t) (small : t < 1)
    (F : K.SkirtTailFamily Z (K.projectedVertex origin))
    (w : C.Vertex Set.univ) (nonroot : w ∉ M.parents.roots) :
    LocalRadialGrowth (M.extendedGeometricCuts F) (K.projectedVertex origin)
      (K.projectedVertex w) := by
  let e : {v : C.Vertex Set.univ // v ∉ M.parents.roots} := ⟨w, nonroot⟩
  exact (localRadialGrowth_of_segment_strict
    (fun nonnegative ordered => M.parent_segment_strict_radial positive small e
      nonnegative ordered) (left_mem_segment ℝ _ _) (M.projected_parent_ne e)).mono
    (fun _ member => Or.inl (Set.mem_iUnion.mpr ⟨e, member⟩))

/-- Continuing at parent endpoints prevents subdivision vertices from becoming dead ends. -/
theorem extended_local_growth (positive : 0 < t) (small : t < 1)
    (F : K.SkirtTailFamily Z (K.projectedVertex origin))
    (rim_covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    {p : Plane} (member : p ∈ M.extendedGeometricCuts F)
    (inside : p ∈ interior (K.clipFootprint Z)) :
    LocalRadialGrowth (M.extendedGeometricCuts F ∩ interior (K.clipFootprint Z))
      (K.projectedVertex origin) p := by
  apply LocalRadialGrowth.inter_open (U := interior (K.clipFootprint Z))
    (open_U := isOpen_interior) (member := inside)
  rcases member with original | skirt
  · obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp original
    by_cases at_parent : p = K.projectedVertex (M.parents.parent e.val)
    · by_cases boundary : C.IsBoundaryVertex Set.univ (M.parents.parent e.val)
      · exact M.extended_growth_on_skirt F (at_parent ▸ rim_covered _ boundary) inside
      · have nonroot : M.parents.parent e.val ∉ M.parents.roots := by
          intro root
          exact boundary ((Set.ext_iff.mp M.roots_eq _).mp root)
        exact at_parent ▸ M.extended_growth_at_nonroot positive small F _ nonroot
    · exact (localRadialGrowth_of_segment_strict
        (fun nonnegative ordered => M.parent_segment_strict_radial positive small e
          nonnegative ordered) on_edge at_parent).mono
        (fun _ on_segment => Or.inl (Set.mem_iUnion.mpr ⟨e, on_segment⟩))
  · exact M.extended_growth_on_skirt F skirt inside

/-- The actual corner-tail construction supplies all the required rim continuations. -/
theorem corner_extended_local_growth (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    ∀ p ∈ M.extendedGeometricCuts F, p ∈ interior (K.clipFootprint Z) →
      LocalRadialGrowth (M.extendedGeometricCuts F ∩ interior (K.clipFootprint Z))
        (K.projectedVertex origin) p := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  have covered (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w) :
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier := by
    obtain ⟨⟨f, k⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ w
    have equal : (K.projectedTriangle f).vertex k = K.projectedVertex w :=
      (K.projectedVertex_ofCorner f k).symm.trans (congrArg K.projectedVertex at_corner)
    have rim : (K.projectedTriangle f).vertex k ∉ interior K.footprint := by
      intro member
      exact ((K.projectedVertex_mem_interior_iff w).mp (equal ▸ member)) boundary
    exact equal ▸ T.cornerTails_original_rim_corner inside source_height lower f k rim
  exact fun _ member interior_point =>
    M.extended_local_growth positive small F covered member interior_point

end Unfoldings.ConvexCap.SectorForest
