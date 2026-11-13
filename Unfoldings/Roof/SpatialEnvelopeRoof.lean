module

public import Unfoldings.Geometry.SpatialEnvelopePairings
public import Unfoldings.Complex.ProjectedEmbedding
public import Unfoldings.Roof.Basic

/-! A conforming supported affine-roof triangulation is an actual embedded convex roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The inherited whole-face projection is the actual prescribed projected triangle. -/
theorem affineProjectedTriangle_eq (i : T.Index) :
    T.pairedComplex.affineProjectedTriangle
      (fun i => (family (T.support i)).project) i = T.projectedTriangle i := by
  apply Triangle.eq_of_vertex_eq
  intro j
  change (family (T.support i)).project
    ((family (T.support i)).project.symm ((T.projectedTriangle i).vertex j)) = _
  exact (family (T.support i)).project.apply_symm_apply _

/-- Complete geometric pairing identifies exactly the same physical projected points. -/
theorem pairedProjection_injective (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    Function.Injective (fun x : T.pairedComplex.Realization Set.univ =>
      Cap.horizontal (T.pairedFolding.toSpace Set.univ x)) := by
  let C := T.pairedComplex
  let A := fun i => (family (T.support i)).project
  have triangles : C.affineProjectedTriangle A = T.projectedTriangle :=
    funext (T.affineProjectedTriangle_eq)
  have joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val :=
    fun s x => (T.paired_seam_projection s x).symm
  have convex : Convex ℝ (⋃ i, (C.affineProjectedTriangle A i).carrier) := by
    rw [triangles, ← T.cover]
    exact AffineEnvelope.convex_clip _ Z
  have conforming' : TriangleFamily.Conforming (C.affineProjectedTriangle A) :=
    triangles.symm ▸ conforming
  have separated : Pairwise (fun i j =>
      Disjoint (interior (C.affineProjectedTriangle A i).carrier)
        (interior (C.affineProjectedTriangle A j).carrier)) := triangles.symm ▸ T.separated
  have complete : ∀ f g : T.Index, f ≠ g → ∀ e d : Fin 3,
      (C.affineProjectedTriangle A f).edge e = (C.affineProjectedTriangle A g).edge d →
      ∃ s, (C.left s = ⟨f, e⟩ ∧ C.right s = ⟨g, d⟩) ∨
        (C.left s = ⟨g, d⟩ ∧ C.right s = ⟨f, e⟩) := by
    intro f g different e d same
    rw [triangles] at same
    exact TriangleFamily.pairedComplex_complete T.projectedTriangle T.separated different same
  intro x y same
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) y
  change Cap.horizontal (T.placement a.1 a.2.val) = Cap.horizontal (T.placement b.1 b.2.val) at same
  dsimp only [placement] at same
  rw [(family (T.support a.1)).horizontal_place,
    (family (T.support b.1)).horizontal_place] at same
  exact (C.point_eq_iff Set.univ a b).mpr
    (C.related_of_affine_projection_eq A joined convex conforming' separated complete a b same)

theorem pairedFolding_footprint : Cap.horizontal '' T.pairedFolding.surface = clip family Z := by
  rw [T.pairedFolding_surface, surface, Set.image_image]
  have same : (fun p => Cap.horizontal (point family p)) = id := funext (horizontal_point family)
  rw [same, Set.image_id]

/-- Supporting planes, complete original physical pairings, and a conforming partition
construct all the geometric roof fields; no embedding or disk certificate is supplied. -/
def roof (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) : ConvexRoof T.pairedComplex where
  folding := T.pairedFolding
  normal := T.normal
  normal_unit i := (family (T.support i)).normal_unit
  normal_upward i := (family (T.support i)).normal_upward
  normal_tangent i := (family (T.support i)).normal_tangent
  supporting i j x := by
    change inner ℝ (family (T.support i)).normal
      (T.placement j x.val - (family (T.support i)).place 0) ≤ 0
    rw [T.placement_eq_point j x.property]
    exact point_supporting family (T.support i) _
  projection_injective := T.pairedProjection_injective conforming
  convex_projection := by
    rw [T.pairedFolding_footprint]
    exact AffineEnvelope.convex_clip _ Z
  interior_projection := by
    rw [T.pairedFolding_footprint]
    exact inside

end Unfoldings.SpatialEnvelope.Triangulation
