module

public import Unfoldings.Geometry.AffineArrangementLocalCone
public import Unfoldings.Geometry.LocalConeClosure

/-! Active conical germs and exact attachment tests for finite affine-cell cut sets. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.AffineArrangement

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite I] (f : I → E →ᵃ[ℝ] ℝ) (signs : I → Bool)

open Classical in
/-- At a nonincident point the cell has the empty germ; otherwise use its actual active cone. -/
def cellGerm (x : E) : Set E :=
  if x ∈ closedChamber f signs then tangentCell f signs x else ∅

omit [FiniteDimensional ℝ E] [Finite I] in
theorem mem_cellGerm_smul_iff (x v : E) {r : ℝ} (positive : 0 < r) :
    r • v ∈ cellGerm f signs x ↔ v ∈ cellGerm f signs x := by
  classical
  unfold cellGerm
  split
  · exact mem_tangentCell_smul_iff f signs x v positive
  · simp only [Set.mem_empty_iff_false]

/-- Every actual cell, incident or not, agrees locally with its constructed conical germ. -/
theorem eventually_mem_closedChamber_iff_cellGerm (x : E) :
    ∀ᶠ z in 𝓝 x, z ∈ closedChamber f signs ↔ z - x ∈ cellGerm f signs x := by
  classical
  by_cases member : x ∈ closedChamber f signs
  · simpa only [cellGerm, ite_eq_left member] using
      eventually_mem_closedChamber_iff_tangent f signs member
  · filter_upwards [(isClosed_closedChamber f signs).isOpen_compl.mem_nhds member] with z hz
    simp only [cellGerm, ite_eq_right member, Set.mem_empty_iff_false, iff_false]
    exact hz

variable {J K L : Type*} [Finite J] [Finite K] [Finite L]

/-- The actual seam closure has exactly the directions allowed by both incident cells
and excluded by all cut pieces. No bank or safe-attachment certificate is assumed. -/
theorem mem_closure_attachment_iff
    (g : J → E →ᵃ[ℝ] ℝ) (otherSigns : J → Bool)
    (cut : K → L → E →ᵃ[ℝ] ℝ) (cutSigns : K → L → Bool) (x : E) :
    x ∈ closure ((closedChamber f signs ∩ closedChamber g otherSigns) \
      (⋃ k, closedChamber (cut k) (cutSigns k))) ↔
      ((cellGerm f signs x ∩ cellGerm g otherSigns x) \
        (⋃ k, cellGerm (cut k) (cutSigns k) x)).Nonempty := by
  have cut_near : ∀ᶠ z in 𝓝 x, ∀ k,
      z ∈ closedChamber (cut k) (cutSigns k) ↔
        z - x ∈ cellGerm (cut k) (cutSigns k) x :=
    eventually_all.mpr (fun k => eventually_mem_closedChamber_iff_cellGerm (cut k) (cutSigns k) x)
  have near : ∀ᶠ z in 𝓝 x,
      z ∈ ((closedChamber f signs ∩ closedChamber g otherSigns) \
        (⋃ k, closedChamber (cut k) (cutSigns k))) ↔
      z - x ∈ ((cellGerm f signs x ∩ cellGerm g otherSigns x) \
        (⋃ k, cellGerm (cut k) (cutSigns k) x)) := by
    filter_upwards [eventually_mem_closedChamber_iff_cellGerm f signs x,
      eventually_mem_closedChamber_iff_cellGerm g otherSigns x, cut_near] with z first last cuts
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion, first, last, cuts]
  obtain ⟨r, positive, local_eq⟩ := Metric.mem_nhds_iff.mp near
  apply mem_closure_iff_nonempty_of_local_cone _ positive
    (fun z near => local_eq (Metric.mem_ball.mpr near))
  intro v t tpos
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion,
    mem_cellGerm_smul_iff _ _ _ _ tpos]

end Unfoldings.AffineArrangement
