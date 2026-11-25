module

public import Unfoldings.Roof.ClippedPhysicalCurvature
public import Unfoldings.Roof.RestrictedBoundaryFrontier
public import Unfoldings.Convex.BoundaryPotential

/-! Clip using only the lifted vertices of the retained faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FiniteDual

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {U : Set Face} (nonempty : U.Nonempty)

/-- The projected vertex of a retained original triangle. -/
def componentDualPoint (i : U × Fin 3) : Plane := K.dualPoint (i.1.val, i.2)

/-- The signed spatial height of a retained original triangle's vertex. -/
def componentDualLevel (i : U × Fin 3) : ℝ := K.dualLevel (i.1.val, i.2)

local notation "point" => K.componentDualPoint (U := U)
local notation "level" => K.componentDualLevel (U := U)

/-- The clipped conjugate formed from the vertices of the retained faces. -/
def componentClippedExtension {slopes : Set Plane} (compact : IsCompact slopes)
    (inhabited : slopes.Nonempty) : SlopeEnvelope := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  exact FiniteDual.clipped point level slopes compact inhabited

/-- An original supporting slope that attains the full extension at a retained
vertex remains active in the restricted extension. -/
theorem componentClippedExtension_active_of_retained_corner {slopes : Set Plane}
    (compact : IsCompact slopes) (inhabited : slopes.Nonempty)
    (i : U × Fin 3) {p : Plane} (active : (K.clippedExtension slopes compact inhabited).Active
      (point i) p)
    (height : (K.clippedExtension slopes compact inhabited).height
      (point i) = level i) :
    (K.componentClippedExtension nonempty compact inhabited).Active
      (point i) p := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  letI : Nonempty Face := K.nonempty_face
  let G := K.componentClippedExtension nonempty compact inhabited
  change p ∈ slopes ∧ (K.clippedExtension slopes compact inhabited).height (point i) =
    inner ℝ (point i) p - K.dualCost p at active
  have active_eq := active.2
  rw [height] at active_eq
  have bounded_cost : K.dualCost p ≤ cost point level p := by
    have bound := vertex_le point level p i
    change K.dualCost p ≤ cost point level p
    linarith only [active_eq, bound]
  have restricted : cost point level p ≤ K.dualCost p := by
    apply cost_le point level
    intro j
    exact vertex_le K.dualPoint K.dualLevel p (j.1.val, j.2)
  have cost_eq := le_antisymm restricted bounded_cost
  have at_most : G.height (point i) ≤ level i := by
    obtain ⟨q, hq⟩ := G.exists_active (point i)
    have bound := vertex_le point level q i
    have hq_eq := hq.2
    change G.height (point i) = inner ℝ (point i) q - cost point level q at hq_eq
    linarith only [hq_eq, bound]
  have at_least := G.affine_le (point i) active.1
  change inner ℝ (point i) p - cost point level p ≤ G.height _ at at_least
  change p ∈ slopes ∧ G.height _ = inner ℝ (point i) p - cost point level p
  refine ⟨active.1, le_antisymm ?_ at_least⟩
  linarith only [at_most, cost_eq, active_eq]

/-- The restricted extension preserves each selected original triangle exactly. -/
theorem componentClippedExtension_preserves_face {slopes : Set Plane}
    (compact : IsCompact slopes) (inhabited : slopes.Nonempty) (f : U)
    (selected : K.normalSlope f.val ∈ slopes) {x : Plane}
    (member : x ∈ (K.projectedTriangle f.val).carrier) :
    (K.componentClippedExtension nonempty compact inhabited).height x = -K.roofHeight x := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  have support (j : U × Fin 3) :
      inner ℝ (point j) (K.normalSlope f.val) - K.supportHeight f.val 0 ≤ level j :=
    K.dual_face_support f.val (j.1.val, j.2)
  have contact (i : Fin 3) :
      level (f, i) = inner ℝ (point (f, i)) (K.normalSlope f.val) - K.supportHeight f.val 0 :=
    K.dual_face_contact f.val i
  have inside : x ∈ FiniteDual.face point level (K.normalSlope f.val) (-K.supportHeight f.val 0) := by
    apply convexHull_mono _ member
    rintro _ ⟨i, rfl⟩
    exact ⟨(f, i), rfl, by simpa only [← sub_eq_add_neg] using contact i⟩
  have equal := FiniteDual.clipped_preserves_face point level compact inhabited
    (s := K.normalSlope f.val) (c := -K.supportHeight f.val 0)
    (fun i => by simpa only [← sub_eq_add_neg] using support i)
    ⟨(f, 0), by simpa only [← sub_eq_add_neg] using contact 0⟩ selected inside
  change (K.componentClippedExtension nonempty compact inhabited).height x =
    inner ℝ x (K.normalSlope f.val) + -K.supportHeight f.val 0 at equal
  rw [K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f.val member, K.supportHeight_gradient]
  linarith only [equal]

theorem componentClippedExtension_original_face_active {slopes : Set Plane}
    (compact : IsCompact slopes) (inhabited : slopes.Nonempty) (f : U)
    (selected : K.normalSlope f.val ∈ slopes) {x : Plane}
    (member : x ∈ (K.projectedTriangle f.val).carrier) :
    (K.componentClippedExtension nonempty compact inhabited).Active x (K.normalSlope f.val) := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  refine ⟨selected, ?_⟩
  rw [K.componentClippedExtension_preserves_face nonempty compact inhabited f selected member,
    K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f.val member]
  change -K.supportHeight f.val x = inner ℝ x (K.normalSlope f.val) -
    cost point level (K.normalSlope f.val)
  have support (j : U × Fin 3) :
      inner ℝ (point j) (K.normalSlope f.val) - K.supportHeight f.val 0 ≤ level j :=
    K.dual_face_support f.val (j.1.val, j.2)
  have contact : level (f, 0) =
      inner ℝ (point (f, 0)) (K.normalSlope f.val) - K.supportHeight f.val 0 :=
    K.dual_face_contact f.val 0
  rw [cost_at_support point level (c := -K.supportHeight f.val 0)
    (fun j => by simpa only [← sub_eq_add_neg] using support j)
    ⟨(f, 0), by simpa only [← sub_eq_add_neg] using contact⟩, K.supportHeight_gradient]
  ring

/-- The entire open contact ray avoids the closed original component. -/
theorem componentClippedExtension_ray_avoids {slopes : Set Plane}
    (compact : IsCompact slopes) (inhabited : slopes.Nonempty) {p x u : Plane} {c t : ℝ}
    (active : (K.componentClippedExtension nonempty compact inhabited).Active x p)
    (side : inner ℝ u p = c) (support : ∀ q ∈ slopes, inner ℝ u q ≤ c)
    (direction : u ≠ 0) (time : 0 < t)
    (selected : ∀ f ∈ U, K.normalSlope f ∈ interior slopes) :
    x + t • u ∉ K.restrictedCarrier U := by
  intro member
  obtain ⟨f, inside⟩ := Set.mem_iUnion.mp member
  have slope := selected f.val f.property
  have along := K.componentClippedExtension_original_face_active nonempty compact inhabited
    f (interior_subset slope) inside
  exact (K.componentClippedExtension nonempty compact inhabited).active_ray_not_interior
    active side support direction time along slope

/-- A genuine side-interior contact rules out a crossing with an open ray
on any other side, even when that ray starts at a shared polygon corner. -/
theorem componentClippedExtension_contact_rays_disjoint {slopes : Set Plane}
    (compact : IsCompact slopes) (inhabited : slopes.Nonempty)
    {p q x y u v : Plane} {c d : ℝ}
    (first : (K.componentClippedExtension nonempty compact inhabited).Active x p)
    (second : (K.componentClippedExtension nonempty compact inhabited).Active y q)
    (on_first : inner ℝ u p = c) (on_second : inner ℝ v q = d)
    (support_first : ∀ z ∈ slopes, inner ℝ u z ≤ c)
    (support_second : ∀ z ∈ slopes, inner ℝ v z ≤ d)
    (away_from_second : inner ℝ v p ≠ d) :
    Disjoint {z | ∃ s : ℝ, 0 < s ∧ z = x + s • u} {z | ∃ t : ℝ, 0 < t ∧ z = y + t • v} := by
  let G := K.componentClippedExtension nonempty compact inhabited
  apply Set.disjoint_left.mpr
  rintro z ⟨s, spos, first_eq⟩ ⟨t, tpos, last_eq⟩
  have active_first : G.Active z p := by
    rw [first_eq, G.active_ray_iff first on_first support_first spos]
    exact ⟨first, on_first⟩
  rw [last_eq, G.active_ray_iff second on_second support_second tpos] at active_first
  exact away_from_second active_first.2

/-- All full-dimensional active slope cells are at retained lifted vertices. -/
theorem componentClippedExtension_full_cell_retained_corner {slopes : Set Plane}
    (compact : IsCompact slopes) (inhabited : slopes.Nonempty) (x : Plane)
    (full : (interior {p |
      (K.componentClippedExtension nonempty compact inhabited).Active x p}).Nonempty) :
    ∃ i : U × Fin 3, point i = x ∧
      (K.componentClippedExtension nonempty compact inhabited).height x =
        level i := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  exact FiniteDual.active_cell_interior_original_vertex point level compact inhabited x full

/-- Component clipping over a compact polygon is still a finite affine envelope. -/
theorem exists_finite_componentClippedExtension {J : Type u} [Fintype J] [Nonempty J]
    (domain : J → Plane →ᵃ[ℝ] ℝ) {Z : ℝ}
    (compact : IsCompact (AffineEnvelope.clip domain Z)) {q : Plane}
    (higher : Z < AffineEnvelope.height domain q) :
    let G := K.componentClippedExtension nonempty compact ⟨q, higher.le⟩
    ∃ (vertices : Finset Plane) (present : vertices.Nonempty),
      (∀ p ∈ vertices, p ∈ G.slopes) ∧
      ∀ x : Plane, G.height x = vertices.sup' present (fun p => G.affine p x) := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  exact FiniteDual.exists_finite_clipped_extension point level domain compact higher

/-- Realize the component-specific envelope by its actual spatial support planes. -/
def componentClippedPhysicalModel {J : Type u} [Fintype J] [Nonempty J]
    (domain : J → Plane →ᵃ[ℝ] ℝ) {Z : ℝ}
    (compact : IsCompact (AffineEnvelope.clip domain Z)) {q : Plane}
    (higher : Z < AffineEnvelope.height domain q) :
    (K.componentClippedExtension nonempty compact ⟨q, higher.le⟩).FiniteSlopeModel :=
  Classical.choice (by
    obtain ⟨vertices, present, within, realizes⟩ :=
      K.exists_finite_componentClippedExtension nonempty domain compact higher
    exact ⟨⟨vertices, present, within, realizes⟩⟩)

section PhysicalModel

variable {slopes : Set Plane} (compact : IsCompact slopes) (inhabited : slopes.Nonempty)
  (M : (K.componentClippedExtension nonempty compact inhabited).FiniteSlopeModel)
  {Z : ℝ} (T : SpatialEnvelope.Triangulation M.plane Z)
  (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (SpatialEnvelope.clip M.plane Z)).Nonempty)

local instance componentClippedIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Meshing adds no positive curvature outside the retained sites. -/
theorem componentClippedPhysical_positive_curvature_retained_corner (convex : Convex ℝ slopes)
    (v : T.pairedComplex.Vertex Set.univ)
    (curved : 0 < T.pairedComplex.interiorAngularDefect Set.univ v) :
    let x := (T.roof conforming inside).projectedVertex v
    ∃ i : U × Fin 3, point i = x ∧
      (K.componentClippedExtension nonempty compact inhabited).height x = level i := by
  classical
  letI : Nonempty U := nonempty.coe_sort
  exact K.componentClippedExtension_full_cell_retained_corner nonempty compact inhabited _
    (M.active_cell_interior_of_positive_curvature T conforming inside convex
      (FiniteDual.convex_cost point level) v curved)

end PhysicalModel

end Unfoldings.ConvexRoof
