module

public import Unfoldings.Roof.AffineFloorSignedComparison
public import Unfoldings.Roof.AffineFloorSharpWindows

/-! Signed comparison on every interval of the actual saved original bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

theorem trimEnds_chord_inner_pos {n : ℕ} (P : PolygonalChain Plane (n + 2))
    (acute : ∀ i j, 0 < inner ℝ (P.edge i) (P.edge j))
    (a b : unitInterval) (first : (a : ℝ) < 1) (last : 0 < (b : ℝ)) (i : Fin (n + 2)) :
    0 < inner ℝ ((P.trimEnds a b).vertex (Fin.last (n + 2)) - (P.trimEnds a b).vertex 0)
      ((P.trimEnds a b).edge i) := by
  rw [← (P.trimEnds a b).sum_edge, sum_inner]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro j _
  rw [P.trimEnds_edge a b i, P.trimEnds_edge a b j, real_inner_smul_left, real_inner_smul_right]
  have h (j : Fin (n + 2)) :
      0 < (if j.val = 0 then 1 - (a : ℝ) else if j.val = n + 1 then (b : ℝ) else 1) := by
    split
    · exact sub_pos.mpr first
    · split
      · exact last
      · exact zero_lt_one
  exact mul_pos (h j) (mul_pos (h i) (acute j i))

theorem trimEnds_reorient {n : ℕ} (P : PolygonalChain Plane (n + 2))
    (E : Plane ≃ₗᵢ[ℝ] Plane) (a b : unitInterval) :
    (P.trimEnds a b).reorient E = (P.reorient E).trimEnds a b := by
  change (⟨fun j => E (if j.val = 0 then P.point 0 a else
      if j.val = n + 2 then P.point (Fin.last (n + 1)) b else P.vertex j)⟩ : PolygonalChain Plane (n + 2)) =
    ⟨fun j => if j.val = 0 then (P.reorient E).point 0 a else
      if j.val = n + 2 then (P.reorient E).point (Fin.last (n + 1)) b else (P.reorient E).vertex j⟩
  congr 1
  funext j
  split_ifs <;> simp only [PolygonalChain.point, reorient_vertex, lineMap_reorient]

end Unfoldings.PolygonalChain

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedBoundaryChain_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) {retain : Set C.Seam}
    {n : ℕ} (bank : (C.boundarySystem retain).Chain n) :
    (K.reorient E).folding.projectedBoundaryChain bank = (K.folding.projectedBoundaryChain bank).reorient E := by
  have equality (i : Fin (n + 2)) :
      ((K.reorient E).folding.projectedBoundaryChain bank).vertex i =
        E ((K.folding.projectedBoundaryChain bank).vertex i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [← Fin.succ_last, (K.reorient E).projectedBoundaryChain_finish_germ,
        K.projectedBoundaryChain_finish_germ]
      exact K.projectFace_reorient E _ _
    · rw [(K.reorient E).projectedBoundaryChain_start_germ, K.projectedBoundaryChain_start_germ]
      exact K.projectFace_reorient E _ _
  exact congrArg PolygonalChain.mk (funext equality)

end Unfoldings.ConvexRoof

namespace Unfoldings.SpatialEnvelope.FloorMesh

open PlanarTopology Real

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance signedWindowIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local notation "K" => T.roof inside

section OneWindow

variable (E : Plane ≃ₗᵢ[ℝ] Plane) {retain : Set T.pairedComplex.Seam} {n : ℕ}
  (bank : (T.pairedComplex.boundarySystem retain).Chain (n + 1))

local notation "Q" => ConvexRoof.reorient (T.roof inside) E
local notation "P" => SpatialFolding.projectedBoundaryChain (ConvexRoof.folding Q) bank

open Classical in
set_option maxHeartbeats 2500000 in
/-- The actual trimmed bank in a strict acute cone satisfies the signed cell allowance. -/
theorem abs_projectedMetricHeadingError_le_signed_acute
    (acute : ∀ i j, 0 < inner ℝ ((P).edge i) ((P).edge j))
    (positive : 0 < (Q).projectedGermOrientation bank.first.val)
    (cut : ∀ i, ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge (bank.point i).val))
    (internal : ∀ i : Fin (n + 1),
      (Q).projectedVertex (ConvexRoof.originalBankTurnVertex bank i) ∈ interior (Q).footprint)
    {cell : Set Plane} (compact : IsCompact cell) (convex : Convex ℝ cell)
    (slopes : ∀ i, (family i).normalSlope ∈ cell)
    {φ D : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (pole_area : ∀ p ∈ cell, ∀ q ∈ cell, |orient 0 p q| / 2 ≤ D) :
    |(K).projectedMetricHeadingError bank (Fin.last (n + 1))| ≤
      2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
        (solidAngleMeasure (Cap.gnomonicNormal '' cell)).toReal + D := by
  let P' := P
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have m_pos : 0 < m.val := by norm_num [m]
  have m_small : m.val < 1 := by norm_num [m]
  let G := P'.trimEnds m m
  let A := G.vertex 0
  let B := G.vertex (Fin.last (n + 2))
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
  let lim := 2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
    (solidAngleMeasure (Cap.gnomonicNormal '' cell)).toReal + D
  let value := |(K).projectedMetricHeadingError bank (Fin.last (n + 1))|
  change value ≤ lim
  by_contra! wrong
  let η := (value - lim) / 8
  have tolerance : 0 < η := div_pos (sub_pos.mpr wrong) (by norm_num)
  obtain ⟨R, c, oriented, progress_trim, f, sample, hf, trace, sample_in, estimate⟩ :=
    T.exists_signed_chartComparison E G inside (P'.trimEnds_chord_inner_pos acute m m m_small m_pos)
      (footprint ▸ entire_path) aligned regular_start regular_end compact convex slopes
      nonnegative small tilt pole_area tolerance
  let E' := E.trans R
  let Q' := (K).reorient E'
  let P'' := Q'.folding.projectedBoundaryChain bank
  let G' := G.reorient R
  let A' := G'.vertex 0
  let B' := G'.vertex (Fin.last (n + 2))
  let L := chartClosingMesh T E' G' c inside
  have chain : P'' = P'.reorient R := by
    dsimp only [P'', P', Q']
    rw [(K).projectedBoundaryChain_reorient E', (K).projectedBoundaryChain_reorient E]
    rfl
  have trim : P''.trimEnds m m = G' := by
    rw [chain, ← P'.trimEnds_reorient R m m]
  have progress (i : Fin (n + 2)) : 0 < P''.edge i 0 := by
    have h := progress_trim i
    change 0 < G'.edge i 0 at h
    rw [← trim, P''.trimEnds_edge] at h
    change 0 < (if i.val = 0 then 1 - m.val else if i.val = n + 1 then m.val else 1) * P''.edge i 0 at h
    apply pos_of_mul_pos_right h
    split
    · exact sub_nonneg.mpr m_small.le
    · split
      · exact m_pos.le
      · exact zero_le_one
  have projected (j : T.Index) (p : Plane) : Q'.projectFace j p = R ((Q).projectFace j p) := by
    dsimp only [Q']
    rw [(K).projectFace_reorient E', (K).projectFace_reorient E]
    rfl
  have shift (p q r : Plane) : orient p q r = orient 0 (q - p) (r - p) := by
    simp only [orient, PiLp.zero_apply, sub_zero, PiLp.sub_apply]
  have positive' : 0 < Q'.projectedGermOrientation bank.first.val := by
    rw [ConvexRoof.projectedGermOrientation, projected, projected, projected, shift, ← R.map_sub, ← R.map_sub]
    apply oriented
    rwa [ConvexRoof.projectedGermOrientation, shift] at positive
  have aligned' (j : T.Index) :
      Disjoint (interior (E' '' (T.projectedTriangle j).carrier)) (Set.range G'.path) := by
    rw [G.path_range_reorient, show E' '' (T.projectedTriangle j).carrier =
      R '' (E '' (T.projectedTriangle j).carrier) by rw [Set.image_image]; rfl]
    change Disjoint (interior (R.toHomeomorph '' (E '' (T.projectedTriangle j).carrier))) _
    rw [← R.toHomeomorph.image_interior]
    exact (aligned j).image R.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  have path_inside : Set.range G'.path ⊆ interior Q'.footprint := by
    rw [G.path_range_reorient, ConvexRoof.footprint_reorient, show E' '' (K).footprint =
      R '' (E '' (K).footprint) by rw [Set.image_image]; rfl]
    change R '' Set.range G.path ⊆ interior (R.toHomeomorph '' (E '' (K).footprint))
    rw [← R.toHomeomorph.image_interior, ← ConvexRoof.footprint_reorient]
    exact Set.image_mono entire_path
  have bank_estimate := estimate false
  have physical := L.graphBankAngleSum_eq_chartBankCornerSum E' f (A' 0) (B' 0) inside hf
    (fun j => trace.symm ▸ aligned' j) sample sample_in
    (fun j _ hz => chartClosingRoof_interior_avoids_endLines T E' G' c inside j hz)
  have h := Q'.sum_trimmedGraphWindow_eq_neg_headingError bank m m hf progress m_small m_pos
    (trim.symm ▸ trace) (trim.symm ▸ path_inside) cut positive'
  rw [show (Q'.folding.projectedBoundaryChain bank).trimEnds m m = G' from trim] at h
  have heading := (T.chartBankCornerSum_eq_sum_regionalAngleExcess inside E' f (A' 0) (B' 0)).trans h
  change |((L.mesh.roof inside).reorient E').graphBankAngleSum f sample (A' 0) (B' 0) false| ≤
    lim + 4 * η at bank_estimate
  rw [physical, heading, abs_neg, (K).projectedMetricHeadingError_reorient E'] at bank_estimate
  change value ≤ lim + 4 * η at bank_estimate
  dsimp only [η] at bank_estimate
  linarith only [wrong, bank_estimate]

end OneWindow

section FromDirection

variable {retain : Set T.pairedComplex.Seam} {n : ℕ}
  (bank : (T.pairedComplex.boundarySystem retain).Chain (n + 1))

local notation "P" => SpatialFolding.projectedBoundaryChain (ConvexRoof.folding (K)) bank

/-- A common forward direction suffices for the sharp bank bound. The
positive chart orientation is chosen from the actual traversal of this bank. -/
theorem abs_projectedMetricHeadingError_le_signed_of_direction (axis : Plane) (unit : ‖axis‖ = 1)
    (progress : ∀ i, 0 < inner ℝ axis ((P).edge i))
    (acute : ∀ i j, 0 < inner ℝ ((P).edge i) ((P).edge j))
    (cut : ∀ i, ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge (bank.point i).val))
    (internal : ∀ i : Fin (n + 1),
      (K).projectedVertex (ConvexRoof.originalBankTurnVertex bank i) ∈ interior (K).footprint)
    {cell : Set Plane} (compact : IsCompact cell) (convex : Convex ℝ cell)
    (slopes : ∀ i, (family i).normalSlope ∈ cell)
    {φ D : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (pole_area : ∀ p ∈ cell, ∀ q ∈ cell, |orient 0 p q| / 2 ≤ D) :
    |(K).projectedMetricHeadingError bank (Fin.last (n + 1))| ≤
      2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
        (solidAngleMeasure (Cap.gnomonicNormal '' cell)).toReal + D := by
  obtain ⟨E, _, positive⟩ := (K).exists_forwardBankChart bank axis unit progress
  apply T.abs_projectedMetricHeadingError_le_signed_acute inside E bank ?_ positive cut _
    compact convex slopes nonnegative small tilt pole_area
  · intro i j
    rw [(K).projectedBoundaryChain_edge_reorient E, (K).projectedBoundaryChain_edge_reorient E,
      E.inner_map_map]
    exact acute i j
  · intro i
    rw [ConvexRoof.projectedVertex_reorient, ConvexRoof.footprint_reorient]
    change E ((K).projectedVertex (ConvexRoof.originalBankTurnVertex bank i)) ∈
      interior (E.toHomeomorph '' (K).footprint)
    rw [← E.toHomeomorph.image_interior]
    exact Set.mem_image_of_mem E (internal i)


end FromDirection

variable {retain : Set T.pairedComplex.Seam} {m : ℕ}
  (bank : (T.pairedComplex.boundarySystem retain).Chain m)

local notation "P" => SpatialFolding.projectedBoundaryChain (ConvexRoof.folding (K)) bank

/-- The sharp heading discrepancy is uniform on every interval of an actual
original bank, including its initial and terminal subpaths. -/
theorem abs_projectedMetricHeadingError_sub_le_signed_of_direction (axis : Plane) (unit : ‖axis‖ = 1)
    (progress : ∀ i, 0 < inner ℝ axis ((P).edge i))
    (acute : ∀ i j, 0 < inner ℝ ((P).edge i) ((P).edge j))
    (cut : ∀ i, ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge (bank.point i).val))
    (internal : ∀ i : Fin m,
      (K).projectedVertex (T.pairedComplex.vertexForgetCuts (Set.subset_univ retain)
        (T.pairedComplex.boundaryEndVertex retain (bank.point i.succ))) ∈ interior (K).footprint)
    {cell : Set Plane} (compact : IsCompact cell) (convex : Convex ℝ cell)
    (slopes : ∀ i, (family i).normalSlope ∈ cell)
    {φ D : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (D_nonneg : 0 ≤ D)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (pole_area : ∀ p ∈ cell, ∀ q ∈ cell, |orient 0 p q| / 2 ≤ D)
    (i j : Fin (m + 1)) (ordered : i ≤ j) :
    |(K).projectedMetricHeadingError bank i - (K).projectedMetricHeadingError bank j| ≤
      2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
        (solidAngleMeasure (Cap.gnomonicNormal '' cell)).toReal + D := by
  by_cases equal : i = j
  · rw [equal, sub_self, abs_zero]
    have cp : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [pi_pos, nonnegative], small⟩
    have delta : 0 ≤ arcsin ((1 - cos φ) / (1 + cos φ)) :=
      arcsin_nonneg.mpr (div_nonneg (sub_nonneg.mpr (cos_le_one _)) (by positivity))
    positivity
  have before : i.val < j.val := (lt_of_le_of_ne ordered equal : i < j)
  let n := j.val - i.val - 1
  have fits : i.val + (n + 1) ≤ m := by
    have bound := j.isLt
    dsimp only [n]
    omega
  let sub := bank.interval i.val (n + 1) fits
  let A := (K).folding.projectedBoundaryChain sub
  have geometry : A = (P).interval i.val (n + 2) (by omega) :=
    (K).folding.projectedBoundaryChain_interval bank i.val (n + 1) fits
  have forward (l : Fin (n + 2)) : 0 < inner ℝ axis (A.edge l) := by
    rw [geometry, PolygonalChain.interval_edge]
    exact progress _
  have acute_sub (i j : Fin (n + 2)) : 0 < inner ℝ (A.edge i) (A.edge j) := by
    rw [geometry, PolygonalChain.interval_edge, PolygonalChain.interval_edge]
    exact acute _ _
  have sub_internal (l : Fin (n + 1)) :
      (K).projectedVertex (ConvexRoof.originalBankTurnVertex sub l) ∈ interior (K).footprint := by
    let t : Fin m := ⟨i.val + l.val, by have := l.isLt; omega⟩
    have same : sub.point l.succ = bank.point t.succ := by
      change bank.point (bank.intervalIndex i.val (n + 1) fits l.succ) = bank.point t.succ
      apply congrArg bank.point
      apply Fin.ext
      change i.val + (l.val + 1) = i.val + l.val + 1
      omega
    unfold ConvexRoof.originalBankTurnVertex
    rw [same]
    exact internal t
  have estimate := T.abs_projectedMetricHeadingError_le_signed_of_direction inside sub axis unit
    forward acute_sub (fun l => cut (bank.intervalIndex i.val (n + 1) fits l)) sub_internal
    compact convex slopes nonnegative small tilt pole_area
  have phase := (K).projectedMetricHeadingError_interval bank i.val (n + 1) fits (Fin.last (n + 1))
  have last_eq : (⟨i.val + (Fin.last (n + 1)).val, by omega⟩ : Fin (m + 1)) = j := by
    apply Fin.ext
    change i.val + (n + 1) = j.val
    dsimp only [n]
    omega
  rw [last_eq] at phase
  exact (abs_sub_comm _ _).trans_le ((congrArg abs phase).symm.le.trans estimate)

end Unfoldings.SpatialEnvelope.FloorMesh
