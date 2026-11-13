module

public import Unfoldings.Roof.ExtendedGeometricCuts
public import Unfoldings.Roof.ParentRadialGrowth
public import Unfoldings.Geometry.LocalRadialGrowth

/-! Local outward progress on the constructed original cuts and radial skirt continuations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane}

/-- A skirt component has outward progress at every point away from the outer rim. -/
theorem extended_growth_on_skirt (F : K.SkirtTailFamily outer (origin))
    {p : Plane} (member : p ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (inside : p ∈ interior outer) :
    LocalRadialGrowth (M.extendedGeometricCuts F) (origin) p := by
  obtain ⟨c, on_tail⟩ := Set.mem_iUnion.mp member
  have not_tip : p ≠ (F.componentTail c).tip := by
    intro equal
    exact (F.componentTail c).boundary.2 (equal ▸ inside)
  exact ((F.componentTail c).local_growth_of_not_tip on_tail not_tip).mono
    (fun _ on_component => Or.inr (Set.mem_iUnion.mpr ⟨c, on_component⟩))

/-- At an original nonroot vertex the selected original edge supplies local progress. -/
theorem extended_growth_at_nonroot (positive : 0 < t) (small : t < 1)
    (F : K.SkirtTailFamily outer (origin))
    (w : C.Vertex Set.univ) (nonroot : w ∉ M.parents.roots) :
    LocalRadialGrowth (M.extendedGeometricCuts F) (origin)
      (K.projectedVertex w) := by
  let e : {v : C.Vertex Set.univ // v ∉ M.parents.roots} := ⟨w, nonroot⟩
  exact (localRadialGrowth_of_segment_strict
    (fun nonnegative ordered => M.parent_segment_strict_radial positive small e
      nonnegative ordered) (left_mem_segment ℝ _ _) (M.projected_parent_ne e)).mono
    (fun _ member => Or.inl (Set.mem_iUnion.mpr ⟨e, member⟩))

/-- Continuing at parent endpoints prevents subdivision vertices from becoming dead ends. -/
theorem extended_local_growth (positive : 0 < t) (small : t < 1)
    (F : K.SkirtTailFamily outer (origin))
    (rim_covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    {p : Plane} (member : p ∈ M.extendedGeometricCuts F)
    (inside : p ∈ interior outer) :
    LocalRadialGrowth (M.extendedGeometricCuts F ∩ interior outer)
      (origin) p := by
  apply LocalRadialGrowth.inter_open (U := interior outer)
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


end Unfoldings.ConvexRoof.SectorForest
