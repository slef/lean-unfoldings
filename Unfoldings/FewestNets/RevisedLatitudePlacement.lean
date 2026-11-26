module

public import Unfoldings.FewestNets.RevisedLatitudeMeanCount

/-! A single generic placement realizes the global bound on original components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets RevisedLatitudeGrid SpatialRotation MeasureTheory InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
set_option maxHeartbeats 1800000 in
/-- A single generic placement realizes any proved per-selector mean allowance. -/
theorem exists_revisedLatitude_component_placement_le {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (allowance : Selector a → ℝ)
    (mean : ∀ key : Selector a,
      let region := selectorSphere positive small key
      ((∫ g, gaussianSelectedCount N region false g ∂probability) +
        (∫ g, gaussianSelectedCount N region true g ∂probability)) / 2 ≤
        2 * uniformSphere.real region + allowance key) :
    ∃ (T : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a),
      (∀ f, T (N.normal f) ∈ selectorSphere positive small (label f)) ∧
      (∀ f (i : ChordFace a) j, (LatitudeRings.chordBasis (rings_oriented positive small) i).coord j (T (N.normal f)) ≠ 0) ∧
      (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) ≤ 2 + ∑ key, allowance key := by
  classical
  let region (key : Selector a) := selectorSphere positive small key
  let count (b : Bool) (g : SpatialRotation) := ∑ key, gaussianSelectedCount N (region key) b g
  let bound := 2 + ∑ key : Selector a, allowance key
  have integrable (b : Bool) (key : Selector a) :
      Integrable (gaussianSelectedCount N (region key) b) probability := by
    obtain ⟨q, unit, hemisphere⟩ := exists_selectorSphere_hemisphere positive small key
    obtain ⟨closed, convex⟩ := selectorSphere_closed_convex positive small key
    exact P.integrable_gaussianSelectedCount N (region key) convex closed q unit hemisphere b
  have total_integrable (b : Bool) : Integrable (count b) probability :=
    integrable_finsetSum _ (fun key _ => integrable b key)
  have counted (b : Bool) : (∫ g, count b g ∂probability) =
      ∑ key, ∫ g, gaussianSelectedCount N (region key) b g ∂probability :=
    integral_finsetSum _ (fun key _ => integrable b key)
  have mean_bound :
      ((∫ g, count false g ∂probability) + (∫ g, count true g ∂probability)) / 2 ≤ bound := by
    rw [counted false, counted true, ← Finset.sum_add_distrib, Finset.sum_div]
    calc
      _ ≤ ∑ key, (2 * uniformSphere.real (region key) + allowance key) :=
        Finset.sum_le_sum (fun key _ => mean key)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have sum : (∑ key, uniformSphere.real (region key)) = 1 :=
          sum_uniformSphere_real_selectorSphere positive small
        rw [sum, mul_one]
  obtain ⟨b, average⟩ : ∃ b, (∫ g, count b g ∂probability) ≤ bound := by
    by_cases first : (∫ g, count false g ∂probability) ≤ bound
    · exact ⟨false, first⟩
    · refine ⟨true, ?_⟩
      linarith only [mean_bound, lt_of_not_ge first]
  let regular (g : SpatialRotation) := ∀ f (i : ChordFace a) j,
    (LatitudeRings.chordBasis (rings_oriented positive small) i).coord j (orthogonalIsometry g b (N.normal f)) ≠ 0
  let bad := {g | ¬ regular g}
  have null : probability bad = 0 := ae_iff.mp
    (ae_orthogonal_avoids_selector_edges positive small N.normal N.unit b)
  obtain ⟨g, good, below⟩ := exists_notMem_null_le_integral (total_integrable b) null
  let T := orthogonalIsometry g b
  have generic : regular g := not_not.mp good
  choose label selected using fun f : Face => exists_selectorSphere positive small (T (N.normal f))
    ((T.norm_map _).trans (N.unit f))
  have exact_label (key : Selector a) : {f | label f = key} =
      {f | siteFlag (region key) b (N.normal f) g = true} := by
    ext f
    change label f = key ↔ _
    rw [Set.mem_ofPred_eq, siteFlag_eq_true_iff, ← orthogonalIsometry_apply]
    constructor
    · exact fun eq => eq ▸ selected f
    · intro inside
      exact selectorSphere_unique positive small (selected f) inside (generic f)
  have actual_count : (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) = count b g := by
    have count_eq := congrArg (fun n : ℕ => (n : ℝ))
      (C.card_labeledComponents_eq_sum_selectedComponents label)
    rw [Nat.cast_sum] at count_eq
    refine count_eq.trans (Finset.sum_congr rfl (fun key _ => ?_))
    unfold gaussianSelectedCount
    rw [exact_label key]
  refine ⟨T, label, selected, generic, ?_⟩
  rw [actual_count]
  exact below.trans average

include P in
/-- A generic orthogonal placement of the original normals has fewer than
296/a⁴ same-selector original face components. -/
theorem exists_revisedLatitude_low_component_placement {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∃ (T : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a),
      (∀ f, T (N.normal f) ∈ selectorSphere positive small (label f)) ∧
      (∀ f (i : ChordFace a) j, (LatitudeRings.chordBasis (rings_oriented positive small) i).coord j (T (N.normal f)) ≠ 0) ∧
      (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) < 296 / a ^ 4 := by
  obtain ⟨T, label, selected, generic, count⟩ :=
    P.exists_revisedLatitude_component_placement_le N positive small selectorCountAllowance
      (P.mean_revisedLatitudeSelectedCount_le N positive small angles)
  exact ⟨T, label, selected, generic, count.trans_lt (selectorCountAllowance_sum_lt positive small)⟩

end Unfoldings.SpatialFolding.ConvexBoundary
