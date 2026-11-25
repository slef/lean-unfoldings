module

public import Unfoldings.Roof.GraphRegionFans
public import Unfoldings.Roof.RestrictedBoundaryCover
public import Unfoldings.Roof.RestrictedBankRays
public import Unfoldings.Roof.RestrictedEmbedding
public import Unfoldings.Roof.SharpRestrictedCorners
public import Unfoldings.Geometry.LocalTwoRays

/-! A Jordan lens has the actual one-sided fan, including at a trimmed endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology Filter Topology InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

private theorem jordan_subset_closure_diff_finite {J V : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (finite : V.Finite) : J ⊆ closure (J \ V) := by
  intro p at_p
  by_contra outside
  let N := (closure (J \ V))ᶜ ∩ (V \ {p})ᶜ
  have open_N : IsOpen N := isClosed_closure.isOpen_compl.inter
    (finite.sdiff (t := {p})).isClosed.isOpen_compl
  have p_in : p ∈ N := ⟨outside, fun h => h.2 (Set.mem_singleton p)⟩
  have only_p (q : Plane) (in_curve : q ∈ J) (near : q ∈ N) : q = p := by
    by_contra different
    have in_V : q ∈ V := by
      by_contra off
      exact near.1 (subset_closure ⟨in_curve, off⟩)
    exact near.2 ⟨in_V, different⟩
  have other : ∃ q ∈ J, q ≠ p := by
    obtain ⟨f, loop, rfl⟩ := jordan
    have separated : f 0 ≠ f (1 / 2) := by
      intro same
      have times := loop.injOn (show (0 : ℝ) ∈ Set.Ico 0 1 from ⟨le_rfl, zero_lt_one⟩)
        (show (1 / 2 : ℝ) ∈ Set.Ico 0 1 from ⟨by norm_num, by norm_num⟩) same
      norm_num at times
    by_cases same : f 0 = p
    · exact ⟨f (1 / 2), ⟨_, ⟨by norm_num, by norm_num⟩, rfl⟩,
        fun eq => separated (same.trans eq.symm)⟩
    · exact ⟨f 0, ⟨0, Schoenflies.zero_mem_I, rfl⟩, same⟩
  obtain ⟨q, at_q, distinct⟩ := other
  have cover : J ⊆ {p} ∪ Nᶜ := fun x hx => by
    by_cases near : x ∈ N
    · exact Or.inl (only_p x hx near)
    · exact Or.inr near
  obtain ⟨x, _, equal, absent⟩ := isPreconnected_closed_iff.mp
    jordan.isConnected.isPreconnected {p} Nᶜ isClosed_singleton open_N.isClosed_compl
    cover ⟨p, at_p, Set.mem_singleton p⟩
      ⟨q, at_q, fun near => distinct (only_p q at_q near)⟩
  exact absent ((Set.mem_singleton_iff.mp equal).symm ▸ p_in)

/-- The entire closed lens is exactly the projected whole-face restriction. -/
theorem restrictedCarrier_graphLensFaces {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
    (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) J) :
    K.restrictedCarrier (K.graphLensFaces J) = closedJordanDomain J := by
  have covered : closedJordanDomain J = ⋃ f ∈ K.graphLensFaces J, (K.projectedTriangle f).carrier := by
    apply TriangleFamily.jordanDomain_eq_selected_triangles K.projectedTriangle jordan
    · rw [← K.footprint_eq_union_projectedTriangles]
      exact K.convex_projection
    · rwa [← K.footprint_eq_union_projectedTriangles]
    · exact aligned
  rw [covered]
  ext p
  simp only [restrictedCarrier, Set.mem_iUnion, Subtype.exists, exists_prop]

open Classical in
set_option maxHeartbeats 1100000 in
/-- A named fine vertex on a lens has a literal boundary fan with the
same regional angle excess. -/
theorem exists_graphLens_boundaryEnd {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
    (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) J)
    (w : C.Vertex Set.univ) (on_curve : K.projectedVertex w ∈ J) :
    let U := K.graphLensFaces J
    ∃ p : (C.restrictFaces U).BoundaryEnd Set.univ,
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) = w ∧
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) = K.projectedVertex w ∧
      K.restrictedBoundaryTurnError U p = -K.regionalAngleExcess U w := by
  let U := K.graphLensFaces J
  let R := C.restrictFaces U
  have region : K.restrictedCarrier U = closedJordanDomain J :=
    K.restrictedCarrier_graphLensFaces jordan contains aligned
  have frontier_eq : frontier (K.restrictedCarrier U) = J := by
    rw [region, frontier_closedJordanDomain jordan]
  have limit : K.projectedVertex w ∈ closure (frontier (K.restrictedCarrier U) \
      Set.range (fun i : Face × Fin 3 => (K.projectedTriangle i.1).vertex i.2)) := by
    rw [frontier_eq]
    exact jordan_subset_closure_diff_finite jordan (Set.finite_range _) on_curve
  obtain ⟨p, original⟩ := K.exists_restricted_boundaryEnd_of_frontier_limit U w limit
  have position : Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) =
      K.projectedVertex w := by
    rw [(K.folding.restrictFaces U).boundaryPosition_raw, ← original]
    exact (K.projectedVertex_ofCorner _ _).symm
  have embedding := K.restrictProjection_injective_of_Jordan U ⟨p.val.1.1.val, p.val.1.1.property⟩
    (frontier_eq.symm ▸ jordan)
  have project (z : R.Vertex Set.univ) :
      K.restrictProjection U (R.vertexPoint Set.univ z) =
        K.projectedVertex (C.includeRestrictedVertexUniv U z) := by
    obtain ⟨⟨f, i⟩, rfl⟩ := R.vertexOfCorner_surjective Set.univ z
    rw [R.vertexPoint_vertexOfCorner]
    rfl
  have unique (z : R.Vertex Set.univ)
      (same : C.includeRestrictedVertexUniv U z =
        C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ p)) :
      z = R.boundaryEndVertex Set.univ p := by
    apply R.vertexPoint_injective Set.univ
    apply embedding
    rw [project, project, same]
  exact ⟨p, original, position,
    (K.restrictedBoundaryTurnError_eq_neg_regional_of_unique U p unique).trans
      (congrArg (fun v => -K.regionalAngleExcess U v) original)⟩

open Classical in
/-- A literal restricted bank germ points along one of the two local
frontier rays. The positive scalar keeps the actual outgoing orientation. -/
theorem restricted_bank_direction_of_local_two_rays (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (u v : Plane)
    (locally : ∀ᶠ x in 𝓝 (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p)),
      x ∈ frontier (K.restrictedCarrier U) →
        x - Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) ∈
          nonnegativeRay u ∪ nonnegativeRay v) :
    (∃ a : ℝ, 0 < a ∧ Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • u) ∨
    (∃ b : ℝ, 0 < b ∧ Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = b • v) := by
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  have genuine : Cap.horizontal (F.germDirection p.val) ≠ 0 := by
    let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
    have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
    rw [← K.horizontal_germDirection] at ray
    exact ray
  apply exists_pos_smul_of_locally_in_two_rays _ _ u v _ genuine _ locally
  intro t member
  let s : unitInterval := ⟨t, member⟩
  have boundary : K.restrictProjection U (R.directedBoundaryPath p s) ∈
      frontier (K.restrictedCarrier U) :=
    K.restricted_boundary_subset_frontier U
      ⟨R.directedBoundaryPath p s, R.directedBoundaryPath_mem_boundary p s, rfl⟩
  rw [K.restrictProjection_directedBoundaryPath] at boundary
  exact boundary

open Classical in
set_option maxHeartbeats 1300000 in
/-- The two actual local rays at a trimmed lens endpoint give the sharp
one-plane bound when its bank ray follows the support crease. -/
theorem abs_graphLens_regionalAngleExcess_le_sharp_of_crease_ray {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) J)
    (w : C.Vertex Set.univ) (at_w : K.projectedVertex w ∈ J) {a b u v : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) = w →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) u = 0)
    (locally : ∀ᶠ x in 𝓝 (K.projectedVertex w),
      x ∈ J → x - K.projectedVertex w ∈ nonnegativeRay u ∪ nonnegativeRay v)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |K.regionalAngleExcess (K.graphLensFaces J) w| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
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
    exact locally
  have local_last : ∀ᶠ z in 𝓝 (Cap.horizontal (F.boundaryPosition q)),
      z ∈ frontier (K.restrictedCarrier U) →
        z - Cap.horizontal (F.boundaryPosition q) ∈ nonnegativeRay u ∪ nonnegativeRay v := by
    rw [F.boundaryPosition_mate p]
    exact local_first
  have nonzero : angle x y ≠ 0 := K.restricted_boundary_rays_angle_ne_zero U p
  have tangent_ray : inner ℝ (a - b) x = 0 ∨ inner ℝ (a - b) y = 0 := by
    rcases K.restricted_bank_direction_of_local_two_rays U p u v local_first with
      ⟨m, _, same⟩ | ⟨m, mp, same⟩
    · left
      change inner ℝ (a - b) (Cap.horizontal (F.germDirection p.val)) = 0
      rw [same, real_inner_smul_right, tangent, mul_zero]
    rcases K.restricted_bank_direction_of_local_two_rays U q u v local_last with
      ⟨n, _, last⟩ | ⟨n, np, last⟩
    · right
      change inner ℝ (a - b) (Cap.horizontal (F.germDirection q.val)) = 0
      rw [last, real_inner_smul_right, tangent, mul_zero]
    exfalso
    change x = m • v at same
    change y = n • v at last
    have genuine : v ≠ 0 := by
      intro zero
      let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
      have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
      rw [← K.horizontal_germDirection] at ray
      apply ray
      change x = 0
      rw [same, zero, smul_zero]
    apply nonzero
    rw [same, last, angle_smul_left_of_pos _ _ mp, angle_smul_right_of_pos _ _ np, angle_self genuine]
  have different : y ≠ x := by
    intro same
    have genuine : x ≠ 0 := by
      let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
      have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
      rwa [← K.horizontal_germDirection] at ray
    exact nonzero (same.symm ▸ angle_self genuine)
  have internal := (K.projectedVertex_mem_interior_iff w).mp (inside at_w)
  have error := K.abs_restrictedBoundaryTurnError_le_sharp_of_crease_ray U p
    (original.symm ▸ internal) (fun f i hit => slopes f i (hit.trans original)) tangent_ray
    different nonnegative small tilt
  rwa [turn, abs_neg] at error

end Unfoldings.ConvexRoof
