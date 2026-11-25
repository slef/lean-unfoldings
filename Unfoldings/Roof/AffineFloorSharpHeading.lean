module

public import Unfoldings.Roof.AffineFloorSharpBank
public import Unfoldings.Roof.TrimmedBankAngleSum

/-! The sharp graph-window bound controls the actual untrimmed original bank roll. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedTotalAngle_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (retain : Set C.Seam)
    (w : C.Vertex retain) : (K.reorient E).projectedTotalAngle retain w = K.projectedTotalAngle retain w := by
  classical
  unfold projectedTotalAngle
  apply Finset.sum_congr rfl
  intro d _
  simp only [K.projectedCornerAngle_reorient E]

/-- A change of horizontal isometric coordinates leaves the real bank error unchanged. -/
theorem projectedMetricHeadingError_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) {retain : Set C.Seam}
    {n : ℕ} (bank : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.reorient E).projectedMetricHeadingError bank i = K.projectedMetricHeadingError bank i := by
  simp only [projectedMetricHeadingError, projectedMetricHeading_eq, K.projectedTotalAngle_reorient E]

end Unfoldings.ConvexRoof

namespace Unfoldings.SpatialEnvelope.FloorMesh

open PlanarTopology Real

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (inside : (interior (clipAbove family floor Z)).Nonempty) (E : Plane ≃ₗᵢ[ℝ] Plane)

local instance sharpBankHeadingFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local notation "K" => T.roof inside
local notation "Q" => ConvexRoof.reorient (T.roof inside) E

open Classical in
/-- The original physical window sum agrees with the graph fan formula in that chart. -/
theorem chartBankCornerSum_eq_sum_regionalAngleExcess (f : ℝ → ℝ) (a b : ℝ) :
    T.chartBankCornerSum E f a b =
      ∑ w : T.pairedComplex.Vertex Set.univ, if (Q).projectedVertex w ∈ graphPoint f '' Set.Ioo a b then
        (Q).regionalAngleExcess ((Q).graphWindowFaces f a b) w else 0 := by
  rw [(Q).sum_regionalAngleExcess_on_trace_eq_cornerSum]
  unfold chartBankCornerSum
  apply Finset.sum_congr rfl
  intro d _
  have carrier : ((Q).projectedTriangle d.1).carrier = E '' (T.projectedTriangle d.1).carrier := by
    rw [ConvexRoof.projectedTriangle_reorient_carrier, T.roof_projectedTriangle]
  have position : ((Q).projectedTriangle d.1).vertex d.2 =
      E ((T.projectedTriangle d.1).vertex d.2) := by
    have h := (K).projectFace_reorient E d.1 ((T.triangle d.1).vertex d.2)
    change ((Q).projectedTriangle d.1).vertex d.2 = E (((K).projectedTriangle d.1).vertex d.2) at h
    rwa [T.roof_projectedTriangle] at h
  have weight : ((Q).projectedTriangle d.1).cornerAngle d.2 =
      (T.projectedTriangle d.1).cornerAngle d.2 :=
    ((K).projectedCornerAngle_reorient E d.1 d.2).trans
      (congrArg (fun U : Triangle => U.cornerAngle d.2) (T.roof_projectedTriangle inside d.1))
  simp only [ConvexRoof.graphWindowFaces, Set.mem_ofPred_eq, position, carrier, weight]
  rfl

theorem chartCorner_eq_projected_vertex (i : T.Index × Fin 3) :
    T.chartCorner E i =
      (Q).projectedVertex (T.pairedComplex.vertexOfCorner Set.univ i) := by
  rw [ConvexRoof.projectedVertex_reorient, (K).projectedVertex_ofCorner, T.roof_projectedTriangle]
  rfl

variable {retain : Set T.pairedComplex.Seam} {n : ℕ}
  (bank : (T.pairedComplex.boundarySystem retain).Chain (n + 1))

local notation "P" => SpatialFolding.projectedBoundaryChain (ConvexRoof.folding (Q)) bank

open Classical in
set_option maxHeartbeats 2000000 in
/-- The actual original bank heading has the sharp acute-cone allowance when the
chosen chart follows the bank forward and its interior turns stay inside the roof. -/
theorem abs_projectedMetricHeadingError_le_sharp_acute
    (progress : ∀ i, 0 < ((P).edge i) 0)
    (positive : 0 < (Q).projectedGermOrientation bank.first.val)
    (cut : ∀ i, ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge (bank.point i).val))
    (internal : ∀ i : Fin (n + 1),
      (Q).projectedVertex (ConvexRoof.originalBankTurnVertex bank i) ∈ interior (Q).footprint)
    {φ Ω : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (curvature : ∀ {A : Type u} {equations : A → Plane →ᵃ[ℝ] ℝ}
      (L : T.LineRefinement equations), L.mesh.pairedComplex.totalInteriorAngularDefect Set.univ ≤ Ω) :
    |(K).projectedMetricHeadingError bank (Fin.last (n + 1))| ≤
      2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω := by
  let P' := P
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have m_pos : 0 < m.val := by norm_num [m]
  have m_small : m.val < 1 := by norm_num [m]
  let G := P'.trimEnds m m
  let A := G.vertex 0
  let B := G.vertex (Fin.last (n + 2))
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  have chart_progress := P'.trimEnds_positive_linear_edges m m m_small m_pos x progress
  have first : A ∈ openSegment ℝ ((Q).projectedGermStart (bank.point 0).val)
      ((Q).projectedGermFinish (bank.point 0).val) := by
    rw [show A = G.vertex 0 from rfl, P'.trimEnds_start,
      PolygonalChain.point, (Q).projectedBoundaryChain_start_germ bank 0,
      (Q).projectedBoundaryChain_finish_germ bank 0]
    exact (openSegment_eq_image_lineMap ℝ _ _).superset ⟨m.val, ⟨m_pos, m_small⟩, rfl⟩
  have last : B ∈ openSegment ℝ ((Q).projectedGermStart bank.last.val) ((Q).projectedGermFinish bank.last.val) := by
    rw [show B = G.vertex (Fin.last (n + 2)) from rfl, P'.trimEnds_last,
      PolygonalChain.point, (Q).projectedBoundaryChain_start_germ bank (Fin.last (n + 1)),
      (Q).projectedBoundaryChain_finish_germ bank (Fin.last (n + 1))]
    exact (openSegment_eq_image_lineMap ℝ _ _).superset ⟨m.val, ⟨m_pos, m_small⟩, rfl⟩
  have start_inside : A ∈ interior (Q).footprint :=
    (Q).projectedOpenGermSegment_subset_interior _ (cut 0) first
  have end_inside : B ∈ interior (Q).footprint :=
    (Q).projectedOpenGermSegment_subset_interior _ (cut (Fin.last (n + 1))) last
  have entire (j : Fin (n + 3)) : G.vertex j ∈ interior (Q).footprint := by
    by_cases initial : j.val = 0
    · rwa [show j = 0 from Fin.ext initial]
    by_cases terminal : j.val = n + 2
    · rwa [show j = Fin.last (n + 2) from Fin.ext terminal]
    let i : Fin (n + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have index : i.succ.castSucc = j := by
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    rw [← index, ← (Q).projected_originalBankTurnVertex_eq_trim bank m m i]
    exact internal i
  have entire_path : Set.range G.path ⊆ interior (Q).footprint := by
    rw [G.path_range_eq_segments]
    refine Set.union_subset (Set.singleton_subset_iff.mpr start_inside) ?_
    exact Set.iUnion_subset fun j =>
      (Q).convex_projection.interior.segment_subset (entire j.castSucc) (entire j.succ)
  have footprint : (Q).footprint = E '' clipAbove family floor Z := by
    rw [ConvexRoof.footprint_reorient, T.roof_footprint]
  have aligned (j : T.Index) :
      Disjoint (interior (E '' (T.projectedTriangle j).carrier)) (Set.range G.path) := by
    have carrier : ((Q).projectedTriangle j).carrier = E '' (T.projectedTriangle j).carrier := by
      rw [ConvexRoof.projectedTriangle_reorient_carrier, T.roof_projectedTriangle]
    rw [← carrier]
    exact ((Q).projectedBank_avoids_faceInteriors bank j).mono_right (P'.trimEnds_path_subset m m)
  have regular_start (i : T.Index × Fin 3) : A ≠ T.chartCorner E i := by
    intro equal
    exact (Q).projectedVertex_not_mem_openGermSegment _
      (T.pairedComplex.vertexOfCorner Set.univ i)
      ((equal.trans (T.chartCorner_eq_projected_vertex inside E i)) ▸ first)
  have regular_end (i : T.Index × Fin 3) : B ≠ T.chartCorner E i := by
    intro equal
    exact (Q).projectedVertex_not_mem_openGermSegment _
      (T.pairedComplex.vertexOfCorner Set.univ i)
      ((equal.trans (T.chartCorner_eq_projected_vertex inside E i)) ▸ last)
  obtain ⟨f, hf, _, trace⟩ := G.exists_continuous_graph_of_horizontal (by omega) chart_progress
  have bound := T.abs_chartBankCornerSum_le_sharp E G inside chart_progress
    (footprint ▸ entire_path) aligned regular_start regular_end trace nonnegative small
    (fun c j => tilt ((chartClosingMesh T E G c inside).mesh.support j))
    (fun c => curvature (chartClosingMesh T E G c inside))
  have bank_sum :=
    (T.chartBankCornerSum_eq_sum_regionalAngleExcess inside E f (A 0) (B 0)).trans
      ((Q).sum_trimmedGraphWindow_eq_neg_headingError bank m m hf progress m_small m_pos trace
        entire_path cut positive)
  rw [bank_sum, abs_neg, (K).projectedMetricHeadingError_reorient E] at bound
  exact bound

end Unfoldings.SpatialEnvelope.FloorMesh
