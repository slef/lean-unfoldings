module

public import Unfoldings.Cap.PrescribedClipSegments
public import Unfoldings.Geometry.RadialTailFamily

/-!
# Disjoint actual radial skirt continuations and their whole-edge meshing

Continue a finite prescribed family of skirt seeds toward the outer clip rim.
Nested continuations are merged; the remaining entire components are disjoint,
cover every seed, and avoid the original footprint's interior. Mesh these
segments together with all original cap edges using actual physical triangles.
This does not yet select all required curvature seeds or construct a cut forest.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

structure SkirtTailFamily (Z : ℝ) (q : Plane) where
  origin : q ∈ interior K.footprint
  Index : Type
  finite : Finite Index
  seed : Index → Plane
  member : ∀ i, seed i ∈ K.clipFootprint Z
  outside : ∀ i, seed i ∉ interior K.footprint
  tail : ∀ i, RadialClipTail (K.clipFootprint Z) q (seed i)

/-- Construct actual outward continuations from any finite family of supplied skirt seeds. -/
def skirtTailFamily {q : Plane} (origin : q ∈ interior K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z < 0)
    {J : Type} [Finite J] (seed : J → Plane)
    (member : ∀ i, seed i ∈ K.clipFootprint Z) (outside : ∀ i, seed i ∉ interior K.footprint) :
    K.SkirtTailFamily Z q where
  origin := origin
  Index := J
  finite := inferInstance
  seed := seed
  member := member
  outside := outside
  tail i := radialClipTail
    (K.isCompact_clipFootprint (interior_subset origin) positive lower.le)
    (K.convex_clipFootprint Z)
    (K.original_footprint_in_clip_interior lower (interior_subset origin))
    (member i) (fun equal => outside i (equal.symm ▸ origin))

namespace SkirtTailFamily

variable {K} {Z : ℝ} {q : Plane} (F : K.SkirtTailFamily Z q)

local instance : Finite F.Index := F.finite

abbrev Component := RadialTailFamily.Component F.tail

def componentTail (c : F.Component) :
    RadialClipTail (K.clipFootprint Z) q (F.seed (RadialTailFamily.componentSeed F.tail c)) :=
  RadialTailFamily.componentTail F.tail c

def componentSeed (c : F.Component) : Plane := F.seed (RadialTailFamily.componentSeed F.tail c)

theorem component_member (c : F.Component) : F.componentSeed c ∈ K.clipFootprint Z :=
  F.member _

theorem component_tip_member (c : F.Component) : (F.componentTail c).tip ∈ K.clipFootprint Z :=
  (K.isClosed_clipFootprint Z).frontier_subset (F.componentTail c).boundary

theorem component_tip_height (c : F.Component) : K.roofHeight (F.componentTail c).tip = Z :=
  K.roofHeight_eq_level_of_clip_frontier (F.componentTail c).boundary

theorem component_outside (c : F.Component) {p : Plane}
    (member : p ∈ (F.componentTail c).carrier) : p ∉ interior K.footprint :=
  (F.componentTail c).carrier_not_mem_inner K.convex_projection F.origin (F.outside _) member

theorem components_disjoint (lower : Z < 0) :
    Pairwise (fun c d : F.Component =>
      Disjoint (F.componentTail c).carrier (F.componentTail d).carrier) :=
  RadialTailFamily.components_disjoint F.tail (K.convex_clipFootprint Z)
    (K.original_footprint_in_clip_interior lower (interior_subset F.origin))

/-- Every seed is contained in one complete disjoint outer-rim component. -/
theorem seeds_covered (i : F.Index) : F.seed i ∈ ⋃ c : F.Component, (F.componentTail c).carrier :=
  RadialTailFamily.seeds_covered F.tail i

theorem spatial_components_disjoint (lower : Z < 0) :
    Pairwise (fun c d : F.Component =>
      Disjoint (K.roofPoint '' (F.componentTail c).carrier)
        (K.roofPoint '' (F.componentTail d).carrier)) := by
  have injective : Function.Injective K.roofPoint := by
    intro p r equal
    have projected := congrArg Cap.horizontal equal
    simpa only [K.horizontal_roofPoint] using projected
  intro c d different
  exact Set.disjoint_image_of_injective injective (F.components_disjoint lower different)

abbrev Active := {c : F.Component // F.componentSeed c ≠ (F.componentTail c).tip}

def first (c : F.Active) := F.componentSeed c.val

def last (c : F.Active) := (F.componentTail c.val).tip

theorem different (c : F.Active) : F.first c ≠ F.last c := c.property

/-- Mesh all genuine disjoint skirt continuations while preserving all original physical edges. -/
def mesh (T : K.ClipSpatialTriangles Z) (lower : Z < 0) :
    K.LineAlignedClip Z (K.originalAndSegmentEquations F.first F.last F.different) := by
  let := RadialTailFamily.finiteComponent F.tail
  exact T.preserveSegments lower

/-- Each meshed actual skirt component is exactly a union of whole physical fine edges. -/
theorem meshed_component (T : K.ClipSpatialTriangles Z) (lower : Z < 0) (c : F.Active) :
    let M := F.mesh T lower
    K.roofPoint '' (F.componentTail c.val).carrier =
      ⋃ a : {a : M.partition.Index × Fin 3 //
          (M.partition.projectedTriangle a.1).edge a.2 ⊆ (F.componentTail c.val).carrier},
        M.partition.placement a.val.1 '' (M.partition.triangle a.val.1).edge a.val.2 := by
  exact (F.mesh T lower).spatial_segment_eq_union_subedges c
    (F.component_member c.val) (F.component_tip_member c.val)

end SkirtTailFamily
end Unfoldings.ConvexCap
