module

public import Unfoldings.Roof.Boundary
public import Unfoldings.Geometry.RadialTailFamily

/-! Finite radial skirt continuations between arbitrary nested convex footprints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Geometric continuations need only a compact convex outer domain enclosing the roof. -/
structure SkirtTailFamily (outer : Set Plane) (q : Plane) where
  origin : q ∈ interior K.footprint
  compact : IsCompact outer
  convex : Convex ℝ outer
  encloses : K.footprint ⊆ interior outer
  Index : Type
  finite : Finite Index
  seed : Index → Plane
  member : ∀ i, seed i ∈ outer
  outside : ∀ i, seed i ∉ interior K.footprint
  tail : ∀ i, RadialClipTail outer q (seed i)

/-- Construct all radial tails before choosing the mesh that will contain them as whole edges. -/
def skirtTailFamily {outer : Set Plane} {q : Plane} (origin : q ∈ interior K.footprint)
    (compact : IsCompact outer) (convex : Convex ℝ outer)
    (encloses : K.footprint ⊆ interior outer) {J : Type} [Finite J] (seed : J → Plane)
    (member : ∀ i, seed i ∈ outer) (outside : ∀ i, seed i ∉ interior K.footprint) :
    K.SkirtTailFamily outer q where
  origin := origin
  compact := compact
  convex := convex
  encloses := encloses
  Index := J
  finite := inferInstance
  seed := seed
  member := member
  outside := outside
  tail i := radialClipTail compact convex (encloses (interior_subset origin))
    (member i) (fun equal => outside i (equal.symm ▸ origin))

namespace SkirtTailFamily

variable {K} {outer : Set Plane} {q : Plane} (F : K.SkirtTailFamily outer q)

local instance skirtSeedFinite : Finite F.Index := F.finite

abbrev Component := RadialTailFamily.Component F.tail

def componentTail (c : F.Component) :
    RadialClipTail outer q (F.seed (RadialTailFamily.componentSeed F.tail c)) :=
  RadialTailFamily.componentTail F.tail c

def componentSeed (c : F.Component) : Plane := F.seed (RadialTailFamily.componentSeed F.tail c)

theorem component_member (c : F.Component) : F.componentSeed c ∈ outer := F.member _

theorem component_tip_member (c : F.Component) : (F.componentTail c).tip ∈ outer :=
  F.compact.isClosed.frontier_subset (F.componentTail c).boundary

theorem component_outside (c : F.Component) {p : Plane}
    (member : p ∈ (F.componentTail c).carrier) : p ∉ interior K.footprint :=
  (F.componentTail c).carrier_not_mem_inner K.convex_projection F.origin (F.outside _) member

theorem components_disjoint : Pairwise (fun c d : F.Component =>
    Disjoint (F.componentTail c).carrier (F.componentTail d).carrier) :=
  RadialTailFamily.components_disjoint F.tail F.convex (F.encloses (interior_subset F.origin))

theorem seeds_covered (i : F.Index) : F.seed i ∈ ⋃ c : F.Component, (F.componentTail c).carrier :=
  RadialTailFamily.seeds_covered F.tail i

abbrev Active := {c : F.Component // F.componentSeed c ≠ (F.componentTail c).tip}

def first (c : F.Active) := F.componentSeed c.val

def last (c : F.Active) := (F.componentTail c.val).tip

theorem different (c : F.Active) : F.first c ≠ F.last c := c.property

end SkirtTailFamily
end Unfoldings.ConvexRoof
