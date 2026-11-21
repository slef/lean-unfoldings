module

public import Unfoldings.Roof.PrimalNormalCone
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams
public import Unfoldings.Roof.SeamSegments

/-! Normal cells at points in the relative interiors of actual original seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The two incident faces supply all projected face slopes at an open seam point. -/
theorem pointIncidentSlopes_eq_pair_on_seam (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (nonvertex : ¬ (C.triangle (C.left s).face).IsVertex x) :
    K.pointIncidentSlopes (K.projectFace (C.left s).face x.val) =
      {K.normalSlope (C.left s).face, K.normalSlope (C.right s).face} := by
  let a := C.edgePoint (C.left s) x
  let b := C.edgePoint (C.right s) (C.identify s x)
  let p := K.projectFace (C.left s).face x.val
  have joined : K.projectFace (C.right s).face (C.identify s x).val = p := by
    change Cap.horizontal (K.folding.place (C.right s).face (C.identify s x).val) =
      Cap.horizontal (K.folding.place (C.left s).face x.val)
    exact (congrArg Cap.horizontal (K.folding.joined s x)).symm
  ext g
  constructor
  · rintro ⟨f, in_face, rfl⟩
    rw [projectedTriangle, Triangle.affineImage_carrier] at in_face
    obtain ⟨y, hy, equal⟩ := in_face
    let d : C.Total := ⟨f, y, hy⟩
    have same := K.projection_injective (a₁ := C.faceMap Set.univ a.1 a.2)
      (a₂ := C.faceMap Set.univ d.1 d.2) (by
        change Cap.horizontal (K.folding.toSpace Set.univ (C.faceMap Set.univ a.1 a.2)) =
          Cap.horizontal (K.folding.toSpace Set.univ (C.faceMap Set.univ d.1 d.2))
        rw [K.folding.toSpace_faceMap, K.folding.toSpace_faceMap]
        exact equal.symm)
    have relation := (C.point_eq_iff Set.univ a d).mp same
    have regular : ¬ C.IsVertex a := nonvertex
    rcases (C.eqvGen_iff_of_regular Set.univ regular).mp relation with h | cross
    · have face_eq : (C.left s).face = f := congrArg Sigma.fst h
      rw [← face_eq]
      exact Set.mem_insert _ _
    · have known : C.Crosses Set.univ a b := ⟨s, Set.mem_univ _, false, x, rfl, rfl⟩
      have face_eq : (C.right s).face = f :=
        congrArg Sigma.fst (C.crosses_unique regular known cross)
      rw [← face_eq]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · refine ⟨(C.left s).face, ?_, rfl⟩
      rw [projectedTriangle, Triangle.affineImage_carrier]
      exact ⟨x.val, (C.triangle _).edge_subset _ x.property, rfl⟩
    · refine ⟨(C.right s).face, ?_, rfl⟩
      rw [projectedTriangle, Triangle.affineImage_carrier]
      exact ⟨(C.identify s x).val,
        (C.triangle _).edge_subset _ (C.identify s x).property, joined⟩

/-- The full slope normal cell at an interior open seam point is the segment
between its two actual face slopes. -/
theorem primalNormalCell_eq_segment_on_seam (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (nonvertex : ¬ (C.triangle (C.left s).face).IsVertex x)
    (inside : K.projectFace (C.left s).face x.val ∈ interior K.footprint) :
    K.primalNormalCell (K.projectFace (C.left s).face x.val) =
      segment ℝ (K.normalSlope (C.left s).face) (K.normalSlope (C.right s).face) := by
  rw [K.primalNormalCell_eq_incident_hull inside,
    K.pointIncidentSlopes_eq_pair_on_seam s x nonvertex, convexHull_pair]

/-- Along an affine part of the roof, normal slopes at an intermediate point
are exactly the slopes that support both endpoints. -/
theorem primalNormalCell_eq_inter_of_affine {a b p : Plane} {t : ℝ}
    (a_mem : a ∈ K.footprint) (b_mem : b ∈ K.footprint) (t_pos : 0 < t) (t_small : t < 1)
    (location : p = (1 - t) • a + t • b)
    (height : K.roofHeight p = (1 - t) * K.roofHeight a + t * K.roofHeight b) :
    K.primalNormalCell p = K.primalNormalCell a ∩ K.primalNormalCell b := by
  have p_mem : p ∈ K.footprint := location ▸
    K.convex_projection a_mem b_mem (sub_nonneg.mpr t_small.le) t_pos.le (by ring)
  ext g
  rw [Set.mem_inter_iff, K.primalNormalCell_iff_dual p_mem, K.primalNormalCell_iff_dual a_mem,
    K.primalNormalCell_iff_dual b_mem]
  have cost_a : inner ℝ a g + K.roofHeight a ≤ K.dualCost g := by
    linarith only [K.fenchel_inequality a_mem g]
  have cost_b : inner ℝ b g + K.roofHeight b ≤ K.dualCost g := by
    linarith only [K.fenchel_inequality b_mem g]
  have convex_cost : inner ℝ p g + K.roofHeight p =
      (1 - t) * (inner ℝ a g + K.roofHeight a) + t * (inner ℝ b g + K.roofHeight b) := by
    rw [height, location, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  rw [convex_cost]
  constructor
  · intro equal
    have first_diff : 0 ≤ (1 - t) * (K.dualCost g - (inner ℝ a g + K.roofHeight a)) :=
      mul_nonneg (sub_nonneg.mpr t_small.le) (sub_nonneg.mpr cost_a)
    have last_diff : 0 ≤ t * (K.dualCost g - (inner ℝ b g + K.roofHeight b)) :=
      mul_nonneg t_pos.le (sub_nonneg.mpr cost_b)
    have zero_first : (1 - t) * (K.dualCost g - (inner ℝ a g + K.roofHeight a)) = 0 := by
      linarith only [equal, first_diff, last_diff]
    have zero_last : t * (K.dualCost g - (inner ℝ b g + K.roofHeight b)) = 0 := by
      linarith only [equal, first_diff, last_diff]
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp zero_first).resolve_left (sub_pos.mpr t_small).ne'),
      sub_eq_zero.mp ((mul_eq_zero.mp zero_last).resolve_left t_pos.ne')⟩
  · rintro ⟨ha, hb⟩
    rw [← ha, ← hb]
    ring

/-- The normal cells of the two original seam endpoints meet in exactly the
segment between the incident face slopes, provided an endpoint is interior. -/
theorem primalNormalCell_inter_endpoints_eq_segment (s : C.Seam)
    (interior_endpoint : K.projectedVertex (C.seamVertex s false) ∈ interior K.footprint ∨
      K.projectedVertex (C.seamVertex s true) ∈ interior K.footprint) :
    K.primalNormalCell (K.projectedVertex (C.seamVertex s false)) ∩
      K.primalNormalCell (K.projectedVertex (C.seamVertex s true)) =
        segment ℝ (K.normalSlope (C.left s).face) (K.normalSlope (C.right s).face) := by
  let f := (C.left s).face
  let e := (C.left s).edge
  let T := C.triangle f
  let a := K.projectedVertex (C.seamVertex s false)
  let b := K.projectedVertex (C.seamVertex s true)
  let x := (1 - (1 / 2 : ℝ)) • T.vertex e + (1 / 2 : ℝ) • T.vertex (Triangle.next e)
  have in_open : x ∈ openSegment ℝ (T.vertex e) (T.vertex (Triangle.next e)) :=
    ⟨1 - 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  let x' : T.Edge e := ⟨x, (openSegment_subset_segment ℝ _ _) in_open⟩
  have nonvertex : ¬ T.IsVertex x := T.not_isVertex_of_mem_openSegment e in_open
  let p := K.projectFace f x
  have location : p = (1 - (1 / 2 : ℝ)) • a + (1 / 2 : ℝ) • b := by
    change (K.projectFace f)
      ((1 - (1 / 2 : ℝ)) • T.vertex e + (1 / 2 : ℝ) • T.vertex (Triangle.next e)) = _
    rw [Convex.combo_affine_apply (by norm_num : (1 - (1 / 2 : ℝ)) + 1 / 2 = 1)]
    rfl
  have open_proj : p ∈ openSegment ℝ a b :=
    ⟨1 - 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, location.symm⟩
  have a_face : a ∈ (K.projectedTriangle f).carrier :=
    (K.projectedTriangle f).vertex_mem e
  have b_face : b ∈ (K.projectedTriangle f).carrier :=
    (K.projectedTriangle f).vertex_mem (Triangle.next e)
  have p_face : p ∈ (K.projectedTriangle f).carrier :=
    (K.projectedTriangle f).convex_carrier.segment_subset a_face b_face
      ((openSegment_subset_segment ℝ _ _) open_proj)
  have a_mem : a ∈ K.footprint := by
    rw [K.footprint_eq_union_projectedTriangles]
    exact Set.mem_iUnion.mpr ⟨f, a_face⟩
  have b_mem : b ∈ K.footprint := by
    rw [K.footprint_eq_union_projectedTriangles]
    exact Set.mem_iUnion.mpr ⟨f, b_face⟩
  have p_inside : p ∈ interior K.footprint := by
    rcases interior_endpoint with first | last
    · exact K.convex_projection.openSegment_interior_self_subset_interior first b_mem open_proj
    · exact K.convex_projection.openSegment_self_interior_subset_interior a_mem last open_proj
  have height : K.roofHeight p = (1 - (1 / 2 : ℝ)) * K.roofHeight a +
      (1 / 2 : ℝ) * K.roofHeight b := by
    rw [K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f p_face,
      K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f a_face,
      K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f b_face, location,
      Convex.combo_affine_apply (by norm_num : (1 - (1 / 2 : ℝ)) + 1 / 2 = 1)]
    rfl
  rw [← K.primalNormalCell_eq_inter_of_affine a_mem b_mem
    (by norm_num) (by norm_num) location height]
  exact K.primalNormalCell_eq_segment_on_seam s x' nonvertex p_inside

end Unfoldings.ConvexRoof
