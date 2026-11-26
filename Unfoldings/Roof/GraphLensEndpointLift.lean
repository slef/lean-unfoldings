module

public import Unfoldings.Roof.ClosingEndpointFan
public import Unfoldings.Roof.GraphLensCornerFan

/-! The face on the closing ray realizes the signed endpoint angle comparison. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology InnerProductGeometry Cap PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
set_option maxHeartbeats 1600000 in
/-- The endpoint of a lens within a coordinate halfplane has the exact
one-face corner error. The chosen face contains an initial portion of the
closing ray, identifying its normal with that of the closing link. -/
theorem exists_graphLens_endpointLift {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (aligned : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    (w : C.Vertex Set.univ) (at_w : K.projectedVertex w ∈ J) {a b u v : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) = w →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) u = 0)
    (local_rays : ∀ᶠ x in 𝓝 (K.projectedVertex w),
      x ∈ J → x - K.projectedVertex w ∈ nonnegativeRay u ∪ nonnegativeRay v)
    (halfplane : (∀ x ∈ closedJordanDomain J, K.projectedVertex w 0 ≤ x 0) ∨
      (∀ x ∈ closedJordanDomain J, x 0 ≤ K.projectedVertex w 0)) :
    ∃ (f : Face) (r : ℝ), 0 < r ∧
      K.projectedVertex w ∈ (K.projectedTriangle f).carrier ∧
      K.projectedVertex w + r • v ∈ (K.projectedTriangle f).carrier ∧
      K.regionalAngleExcess (K.graphLensFaces J) w =
        angle (K.sectionDirection f u) (K.sectionDirection f v) - angle u v := by
  let U := K.graphLensFaces J
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  obtain ⟨p, original, position, turn⟩ :=
    K.exists_graphLens_boundaryEnd jordan (inside.trans interior_subset) aligned w at_w
  let q := R.boundaryMate Set.univ p
  let x := Cap.horizontal (F.germDirection p.val)
  let y := Cap.horizontal (F.germDirection q.val)
  have frontier_eq : frontier (K.restrictedCarrier U) = J := by
    rw [K.restrictedCarrier_graphLensFaces jordan (inside.trans interior_subset) aligned,
      frontier_closedJordanDomain jordan]
  have local_first : ∀ᶠ z in 𝓝 (Cap.horizontal (F.boundaryPosition p)),
      z ∈ frontier (K.restrictedCarrier U) →
        z - Cap.horizontal (F.boundaryPosition p) ∈ nonnegativeRay u ∪ nonnegativeRay v := by
    rw [frontier_eq, position]
    exact local_rays
  have local_last : ∀ᶠ z in 𝓝 (Cap.horizontal (F.boundaryPosition q)),
      z ∈ frontier (K.restrictedCarrier U) →
        z - Cap.horizontal (F.boundaryPosition q) ∈ nonnegativeRay u ∪ nonnegativeRay v := by
    rw [F.boundaryPosition_mate p]
    exact local_first
  let w' := C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ p)
  have w_eq : K.projectedVertex w' 0 = K.projectedVertex w 0 :=
    congrArg (fun v => K.projectedVertex v 0) original
  have selected_germ (g : C.LinkGerm Set.univ w') (member : g.val.1.1 ∈ U) :
      Cap.horizontal (K.folding.germFarPoint g.val) ∈ closedJordanDomain J :=
    K.graphLensFace_subset_domain jordan aligned g.val.1.1 member
      ((K.projectedTriangle g.val.1.1).vertex_mem (C.germFarCorner g.val).2)
  have plane : (∀ g : C.LinkGerm Set.univ w', g.val.1.1 ∈ U → 0 ≤ K.projectedGermRay g 0) ∨
      (∀ g : C.LinkGerm Set.univ w', g.val.1.1 ∈ U → K.projectedGermRay g 0 ≤ 0) := by
    rcases halfplane with fwd | back
    · left
      intro g member
      change 0 ≤ Cap.horizontal (K.folding.germFarPoint g.val) 0 - K.projectedVertex w' 0
      rw [w_eq, sub_nonneg]
      exact fwd _ (selected_germ g member)
    · right
      intro g member
      change Cap.horizontal (K.folding.germFarPoint g.val) 0 - K.projectedVertex w' 0 ≤ 0
      rw [w_eq, sub_nonpos]
      exact back _ (selected_germ g member)
  have at_face (e : R.BoundaryEnd Set.univ)
      (e_pos : Cap.horizontal (F.boundaryPosition e) = K.projectedVertex w)
      {t : ℝ} (ray : Cap.horizontal (F.germDirection e.val) = t • v) :
      K.projectedVertex w ∈ (K.projectedTriangle e.val.1.1.val).carrier ∧
      K.projectedVertex w + t • v ∈ (K.projectedTriangle e.val.1.1.val).carrier := by
    have start : (K.projectedTriangle e.val.1.1.val).vertex e.val.1.2 = K.projectedVertex w := by
      rw [F.boundaryPosition_raw] at e_pos
      exact e_pos
    refine ⟨start ▸ (K.projectedTriangle _).vertex_mem _, ?_⟩
    have finish : (K.projectedTriangle e.val.1.1.val).vertex (R.germFarCorner e.val).2 =
        K.projectedVertex w + t • v := by
      rw [← ray, ← e_pos, F.boundaryPosition_raw, SpatialFolding.germDirection, map_sub]
      change Cap.horizontal (F.germFarPoint e.val) =
        Cap.horizontal (F.place e.val.1.1 ((R.triangle e.val.1.1).vertex e.val.1.2)) +
          (Cap.horizontal (F.germFarPoint e.val) -
            Cap.horizontal (F.place e.val.1.1 ((R.triangle e.val.1.1).vertex e.val.1.2)))
      abel
    exact finish ▸ (K.projectedTriangle _).vertex_mem _
  have rays_ne := K.restricted_boundary_rays_angle_ne_zero U p
  have distinct {z : Plane} {s t : ℝ} (sp : 0 < s) (tp : 0 < t)
      (hx : x = s • z) (hy : y = t • z) : False := by
    have zn : z ≠ 0 := by
      intro zero
      let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
      have h := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
      rw [← K.horizontal_germDirection] at h
      apply h
      change x = 0
      rw [hx, zero, smul_zero]
    apply rays_ne
    change angle x y = 0
    rw [hx, hy, angle_smul_left_of_pos _ _ sp, angle_smul_right_of_pos _ _ tp, angle_self zn]
  have attached (f : Face) {s t : ℝ} (sp : 0 < s) (tp : 0 < t) :
      angle (K.sectionDirection f (s • u)) (K.sectionDirection f (t • v)) -
        angle (s • u) (t • v) =
      angle (K.sectionDirection f u) (K.sectionDirection f v) - angle u v := by
    rw [sectionDirection_smul, sectionDirection_smul,
      angle_smul_left_of_pos _ _ sp, angle_smul_right_of_pos _ _ tp,
      angle_smul_left_of_pos _ _ sp, angle_smul_right_of_pos _ _ tp]
  have orig_slopes (f : Face) (i : Fin 3) (hit : C.vertexOfCorner Set.univ (f, i) = w') :
      K.normalSlope f = a ∨ K.normalSlope f = b := slopes f i (hit.trans original)
  rcases K.restricted_bank_direction_of_local_two_rays U p u v local_first with
      ⟨s, sp, hx⟩ | ⟨s, sp, hx⟩ <;>
    rcases K.restricted_bank_direction_of_local_two_rays U q u v local_last with
      ⟨t, tp, hy⟩ | ⟨t, tp, hy⟩
  · exact (distinct sp tp hx hy).elim
  · have e := K.restrictedEndpointTurnError_eq_angle_of_crease U p false orig_slopes plane
      (by change inner ℝ (a - b) x = 0; rw [show x = s • u from hx, real_inner_smul_right, tangent, mul_zero])
    change -K.restrictedBoundaryTurnError U p =
      angle (K.sectionDirection q.val.1.1.val x) (K.sectionDirection q.val.1.1.val y) - angle x y at e
    rw [turn, neg_neg, show x = s • u from hx, show y = t • v from hy,
      attached q.val.1.1.val sp tp] at e
    have pr := (congrArg Cap.horizontal (F.boundaryPosition_mate p)).trans position
    obtain ⟨contains, forward⟩ := at_face q pr hy
    exact ⟨q.val.1.1.val, t, tp, contains, forward, e⟩
  · have e := K.restrictedEndpointTurnError_eq_angle_of_crease U p true orig_slopes plane
      (by change inner ℝ (a - b) y = 0; rw [show y = t • u from hy, real_inner_smul_right, tangent, mul_zero])
    change -K.restrictedBoundaryTurnError U p =
      angle (K.sectionDirection p.val.1.1.val x) (K.sectionDirection p.val.1.1.val y) - angle x y at e
    rw [turn, neg_neg, angle_comm (K.sectionDirection p.val.1.1.val x),
      angle_comm x y, show x = s • v from hx, show y = t • u from hy,
      attached p.val.1.1.val tp sp] at e
    obtain ⟨contains, forward⟩ := at_face p position hx
    exact ⟨p.val.1.1.val, s, sp, contains, forward, e⟩
  · exact (distinct sp tp hx hy).elim

end Unfoldings.ConvexRoof
