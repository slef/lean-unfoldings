module

public import Unfoldings.Geometry.SpatialEnvelope
public import Unfoldings.Geometry.AffineEnvelopeTriangulation
public import Unfoldings.Geometry.CommonTriangleRefinement
public import Unfoldings.Geometry.RefinedConformity
public import Unfoldings.Geometry.TriangleAffine

/-! Physical Euclidean triangles covering a horizontal section of a supported affine roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

universe u

variable {I : Type u} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

/-- A finite geometric triangle partition, with every closed triangle on its actual support. -/
structure Triangulation (Z : ℝ) where
  Index : Type
  finite : Finite Index
  projectedTriangle : Index → Triangle
  support : Index → I
  cover : clip family Z = ⋃ i, (projectedTriangle i).carrier
  separated : Pairwise (fun i j =>
    Disjoint (interior (projectedTriangle i).carrier) (interior (projectedTriangle j).carrier))
  active : ∀ i p, p ∈ (projectedTriangle i).carrier →
    height family p = (family (support i)).height p

/-- A physical roof partition together with its actual side of every prescribed line. -/
structure ConstrainedTriangulation {J : Type u} (extra : J → Plane →ᵃ[ℝ] ℝ) (Z : ℝ)
    extends Triangulation family Z where
  signs : Index → J → Bool
  constrained : ∀ i p, p ∈ (projectedTriangle i).carrier → ∀ j,
    0 ≤ AffineArrangement.signed (extra j) (signs i j) p

/-- Construct an actual finite partition respecting all extra prescribed proper lines. -/
def constrainedTriangulation {J : Type u} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, extra j ≠ 0) {Z : ℝ} (compact : IsCompact (clip family Z))
    {q : Plane} (higher : Z < height family q) :
    ConstrainedTriangulation family extra Z := Classical.choice (by
  obtain ⟨A, finite, triangle, plane, signs, cover, separated, active, constrained⟩ :=
    AffineEnvelope.exists_constrained_triangle_partition (fun i => (family i).height) extra
      proper compact higher
  let : Finite A := finite
  let : Fintype A := Fintype.ofFinite A
  let e := Fintype.equivFin A
  refine ⟨{
    toTriangulation := {
      Index := Fin (Fintype.card A)
      finite := inferInstance
      projectedTriangle := fun i => triangle (e.symm i)
      support := fun i => plane (e.symm i)
      cover := ?_
      separated := fun _ _ different =>
        separated (fun equal => different (e.symm.injective equal))
      active := fun i => active (e.symm i) }
    signs i := signs (e.symm i)
    constrained i := constrained (e.symm i) }⟩
  change AffineEnvelope.clip (fun i => (family i).height) Z = _
  rw [cover]
  ext p
  constructor
  · rintro member
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨e a, by simpa only [e.symm_apply_apply] using ha⟩
  · rintro member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨e.symm i, hi⟩)

namespace Triangulation

variable {family} {Z : ℝ} (T : Triangulation family Z)

/-- The triangle's actual Euclidean coordinates in its own spatial supporting plane. -/
def triangle (i : T.Index) : Triangle :=
  (T.projectedTriangle i).affineImage (family (T.support i)).project.symm.toAffineMap
    (family (T.support i)).project.symm.injective

theorem triangle_carrier (i : T.Index) : (T.triangle i).carrier =
    (family (T.support i)).project.symm '' (T.projectedTriangle i).carrier :=
  (T.projectedTriangle i).affineImage_carrier _ _

def placement (i : T.Index) : Plane →ᵃⁱ[ℝ] Space := (family (T.support i)).place

def normal (i : T.Index) : Space := (family (T.support i)).normal

/-- Each whole spatial triangle lies exactly on the constructed finite supporting roof. -/
theorem placement_eq_point (i : T.Index) {x : Plane} (member : x ∈ (T.triangle i).carrier) :
    T.placement i x = point family ((family (T.support i)).project x) := by
  rw [T.triangle_carrier] at member
  obtain ⟨p, member, rfl⟩ := member
  rw [(family (T.support i)).project.apply_symm_apply]
  exact (point_eq_place family (T.support i) (T.active i p member)).symm

/-- Exact spatial coverage follows from the actual rigid supporting-plane maps. -/
theorem spatial_cover : surface family Z = ⋃ i, T.placement i '' (T.triangle i).carrier := by
  ext z
  constructor
  · rintro ⟨p, member, rfl⟩
    rw [T.cover] at member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    refine Set.mem_iUnion.mpr ⟨i, (family (T.support i)).project.symm p, ?_, ?_⟩
    · rw [T.triangle_carrier]
      exact ⟨p, member, rfl⟩
    · exact (point_eq_place family (T.support i) (T.active i p member)).symm
  · rintro covered
    obtain ⟨i, x, inside, rfl⟩ := Set.mem_iUnion.mp covered
    rw [T.triangle_carrier] at inside
    obtain ⟨p, member, rfl⟩ := inside
    refine ⟨p, ?_, point_eq_place family (T.support i) (T.active i p member)⟩
    rw [T.cover]
    exact Set.mem_iUnion.mpr ⟨i, member⟩

/-- Refine using a single common geometric boundary graph, preserving all support labels. -/
def refined : Triangulation family Z :=
  let := T.finite
  let R := commonTriangleRefinement T.projectedTriangle
  { Index := R.Index
    finite := inferInstance
    projectedTriangle := R.triangle
    support i := T.support i.1
    cover := T.cover.trans R.total_cover
    separated := R.separated T.separated
    active i p member := T.active i.1 p (R.triangle_subset i member) }

theorem refined_conforming : TriangleFamily.Conforming T.refined.projectedTriangle :=
  let := T.finite
  (commonTriangleRefinement T.projectedTriangle).conforming T.separated

end Triangulation
namespace ConstrainedTriangulation

variable {family} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  (T : ConstrainedTriangulation family extra Z)

/-- The common geometric refinement preserves every specified line constraint. -/
def refined : ConstrainedTriangulation family extra Z :=
  let := T.finite
  let R := commonTriangleRefinement T.projectedTriangle
  { toTriangulation := T.toTriangulation.refined
    signs i := T.signs i.1
    constrained i p member := T.constrained i.1 p (R.triangle_subset i member) }

theorem refined_conforming : TriangleFamily.Conforming T.refined.projectedTriangle :=
  T.toTriangulation.refined_conforming

end ConstrainedTriangulation

end Unfoldings.SpatialEnvelope
