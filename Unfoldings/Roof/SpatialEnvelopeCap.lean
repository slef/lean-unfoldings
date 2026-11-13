module

public import Unfoldings.Roof.SpatialEnvelopeRoof
public import Unfoldings.Roof.Boundary
public import Unfoldings.Roof.HorizontalLevelCap

/-! Every conforming compact affine-roof section is an actual horizontal-rim convex cap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Every physical triangle point projects into its actual prescribed horizontal triangle. -/
theorem projected_member (i : T.Index) {x : Plane} (member : x ∈ (T.triangle i).carrier) :
    (family (T.support i)).project x ∈ (T.projectedTriangle i).carrier := by
  rw [T.triangle_carrier] at member
  obtain ⟨p, hp, rfl⟩ := member
  simpa only [(family (T.support i)).project.apply_symm_apply] using hp

/-- Actual intrinsic banks lie exactly in the horizontal clipping plane. -/
theorem bank_height (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (bank : T.pairedComplex.BoundaryBank Set.univ)
    (x : (T.triangle bank.val.face).Edge bank.val.edge) :
    T.placement bank.val.face x.val 2 = Z := by
  let Q := T.roof conforming inside
  have boundary := (Q.projected_mem_frontier_iff_bankBoundary
    (T.pairedComplex.bankMap Set.univ bank x)).mpr
      (T.pairedComplex.bankMap_mem_bankBoundary Set.univ bank x)
  change Cap.horizontal (T.placement bank.val.face x.val) ∈
    frontier (Cap.horizontal '' T.pairedFolding.surface) at boundary
  rw [T.pairedFolding_footprint] at boundary
  have projected : Cap.horizontal (T.placement bank.val.face x.val) =
      (family (T.support bank.val.face)).project x.val :=
    (family (T.support bank.val.face)).horizontal_place x.val
  rw [projected] at boundary
  have level := AffineEnvelope.height_eq_level_of_frontier
    (fun i => (family i).height) boundary
  rw [T.placement_eq_point bank.val.face
    ((T.triangle bank.val.face).edge_subset bank.val.edge x.property), height_point]
  exact level

/-- The assembled Euclidean roof mesh satisfies the full geometric cap interface after
one ambient translation; no acute auxiliary triangulation or unfolding is assumed. -/
def normalizedCap (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) : ConvexCap T.pairedComplex :=
  (T.roof conforming inside).capOfHorizontalLevel Z
    (by
      intro x member
      obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp member
      exact T.bank_height conforming inside bank y)
    (by
      intro i j
      have member := (T.triangle i).vertex_mem j
      have projected := T.projected_member i member
      have in_clip := T.cover.symm.subset (Set.mem_iUnion.mpr ⟨i, projected⟩)
      change Z ≤ T.placement i ((T.triangle i).vertex j) 2
      rw [T.placement_eq_point i member, height_point]
      exact in_clip)

/-- Normalizing the clipping level leaves the actual upward normals and their tilt unchanged. -/
theorem normalizedCap_tilt (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) {φ : ℝ}
    (bound : ∀ i : I, Real.cos φ ≤ (family i).normal 2) :
    (T.normalizedCap conforming inside).TiltBound φ := fun i => bound (T.support i)

theorem normalizedCap_footprint (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) :
    (T.normalizedCap conforming inside).footprint = clip family Z :=
  ((T.roof conforming inside).levelFolding_footprint Z).trans T.pairedFolding_footprint

end Unfoldings.SpatialEnvelope.Triangulation
