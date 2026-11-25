module

public import Unfoldings.Roof.AffineFloorNearChord
public import Unfoldings.Roof.AffineFloorGraphTransfer

/-! Remove the auxiliary closing curve and retain the limiting sharp bound on the original bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

open PlanarTopology Real

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (E : Plane ≃ₗᵢ[ℝ] Plane)

open Classical in
/-- The original bank sum depends only on the graph trace in its window. -/
theorem chartBankCornerSum_congr {f g : ℝ → ℝ} {a b : ℝ}
    (trace : graphPoint f '' Set.Icc a b = graphPoint g '' Set.Icc a b) :
    T.chartBankCornerSum E f a b = T.chartBankCornerSum E g a b := by
  have same : Set.EqOn f g (Set.Icc a b) := by
    intro t within
    obtain ⟨s, _, position⟩ := trace.subset ⟨t, within, rfl⟩
    have x_eq : s = t := congrArg (fun p : Plane => p 0) position
    subst s
    exact (congrArg (fun p : Plane => p 1) position).symm
  have point_eq (t : ℝ) (ht : t ∈ Set.Ioo a b) : graphPoint f t = graphPoint g t := by
    simp only [graphPoint, same (Set.Ioo_subset_Icc_self ht)]
  have same_path : graphPoint f '' Set.Ioo a b = graphPoint g '' Set.Ioo a b := by
    ext p
    constructor
    · rintro ⟨t, ht, equal⟩
      exact ⟨t, ht, (point_eq t ht).symm.trans equal⟩
    · rintro ⟨t, ht, equal⟩
      exact ⟨t, ht, (point_eq t ht).trans equal⟩
  unfold chartBankCornerSum
  apply Finset.sum_congr rfl
  intro d _
  have side : interiorAboveGraph f a b (E '' (T.projectedTriangle d.1).carrier) ↔
      interiorAboveGraph g a b (E '' (T.projectedTriangle d.1).carrier) := by
    simp only [interiorAboveGraph]
    constructor <;> rintro ⟨p, hp, ht, higher⟩ <;> refine ⟨p, hp, ht, ?_⟩
    · rwa [← same (Set.Ioo_subset_Icc_self ht)]
    · rwa [same (Set.Ioo_subset_Icc_self ht)]
  simp only [same_path, side]

variable {n : ℕ} (P : PolygonalChain Plane (n + 1))
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local notation "A" => P.vertex 0
local notation "B" => P.vertex (Fin.last (n + 1))
local notation "Q[" c "]" => chartClosingRoof T E P c inside
local notation "L[" c "]" => chartClosingMesh T E P c inside
local notation "D" => interior (E '' clipAbove family floor Z)

local instance sharpChartIndexFintype (c : Plane) : Fintype (L[c]).mesh.Index :=
  @Fintype.ofFinite _ (L[c]).mesh.finite

private theorem chart_aligned_subset_skeleton (contained : Set.range P.path ⊆ D)
    (aligned : ∀ j, Disjoint (interior (E '' (T.projectedTriangle j).carrier)) (Set.range P.path)) :
    Set.range P.path ⊆ ⋃ i : T.Index × Fin 3,
      segment ℝ (T.chartCorner E i) (T.chartCorner E (i.1, Triangle.next i.2)) := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := interior_subset (contained hz)
  obtain ⟨j, member⟩ := Set.mem_iUnion.mp (T.cover.subset hp)
  have border : p ∈ frontier (T.projectedTriangle j).carrier := by
    refine ⟨subset_closure member, ?_⟩
    intro inside
    have here : E p ∈ interior (E '' (T.projectedTriangle j).carrier) := by
      change E p ∈ interior (E.toHomeomorph '' (T.projectedTriangle j).carrier)
      rw [← E.toHomeomorph.image_interior]
      exact Set.mem_image_of_mem E inside
    exact Set.disjoint_left.mp (aligned j) here hz
  obtain ⟨k, edge⟩ := Set.mem_iUnion.mp ((T.projectedTriangle j).frontier_eq_union_edges ▸ border)
  apply Set.mem_iUnion.mpr
  refine ⟨(j, k), ?_⟩
  let H := E.toLinearEquiv.toAffineEquiv.toAffineMap
  change H p ∈ segment ℝ (H ((T.projectedTriangle j).vertex k))
    (H ((T.projectedTriangle j).vertex (Triangle.next k)))
  rw [← image_segment ℝ H]
  exact Set.mem_image_of_mem H edge

open Classical in
set_option maxHeartbeats 1800000 in
/-- A trimmed bank in the original mesh satisfies the sharp heading bound.
The comparison construction can use any uniform upper bound on its actual
intrinsic curvature, in particular the original selector's area. -/
theorem abs_chartBankCornerSum_le_sharp
    (progress : ∀ i, 0 < (P.edge i) 0) (contained : Set.range P.path ⊆ D)
    (aligned : ∀ j, Disjoint (interior (E '' (T.projectedTriangle j).carrier)) (Set.range P.path))
    (first : ∀ i, (A) ≠ T.chartCorner E i) (last : ∀ i, (B) ≠ T.chartCorner E i)
    {f : ℝ → ℝ} (trace : graphPoint f '' Set.Icc ((A) 0) ((B) 0) = Set.range P.path)
    {φ Ω : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (fine_tilt : ∀ c, (Q[c]).TiltBound φ)
    (curvature : ∀ c, (L[c]).mesh.pairedComplex.totalInteriorAngularDefect Set.univ ≤ Ω) :
    |T.chartBankCornerSum E f ((A) 0) ((B) 0)| ≤ 2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω := by
  let lim := 2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω
  let value := |T.chartBankCornerSum E f ((A) 0) ((B) 0)|
  let scale := 1 + sin φ * tan φ
  have sine : 0 ≤ sin φ := Real.sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos])
  have tangent : 0 ≤ tan φ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two nonnegative small.le
  have scale_pos : 0 < scale := by dsimp only [scale]; positivity
  change value ≤ lim
  by_contra! too_large
  let gap := (value - lim) / 2
  have gap_positive : 0 < gap := half_pos (sub_pos.mpr too_large)
  let η := gap / scale
  have tolerance : 0 < η := div_pos gap_positive scale_pos
  obtain ⟨c, g, sample, hg, graph, sample_in, estimate⟩ :=
    T.exists_chartComparison_nearChord E P inside progress contained
      (chart_aligned_subset_skeleton T E P contained aligned) first last nonnegative small fine_tilt tolerance
  let L := L[c]
  have same_bank := L.graphBankAngleSum_eq_chartBankCornerSum E g ((A) 0) ((B) 0) inside hg
    (fun j => graph.symm ▸ aligned j) sample sample_in
    (fun j _ hz => chartClosingRoof_interior_avoids_endLines T E P c inside j hz)
  have equal : (Q[c]).graphBankAngleSum g sample ((A) 0) ((B) 0) false =
      T.chartBankCornerSum E f ((A) 0) ((B) 0) :=
    same_bank.trans (T.chartBankCornerSum_congr E (graph.trans trace.symm))
  have original := (congrArg abs equal).symm.le.trans (estimate false)
  have extra : scale * η = gap := by
    change scale * (gap / scale) = gap
    exact (mul_comm scale (gap / scale)).trans (div_mul_cancel₀ gap scale_pos.ne')
  change value ≤ (L[c]).mesh.pairedComplex.totalInteriorAngularDefect Set.univ +
    2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + scale * η at original
  rw [extra] at original
  dsimp only [gap, lim] at original too_large
  linarith only [original, curvature c, too_large]

end Unfoldings.SpatialEnvelope.FloorMesh
