module

public import Unfoldings.Cap.JordanLocalSection
public import Unfoldings.Cap.JordanBankPositions
public import Unfoldings.Cap.SharpRestrictedSectionSum

/-! Sharp total turn for an actual regular straight connector in a Jordan contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- The sharp absolute turn sum along a straight connector is at most twice
the tilt times its sine. Only geometric regularity of the selected contacts
enters the local proofs. -/
theorem sum_abs_jordan_closing_link_error_le_sin_tilt (inside : J ⊆ interior K.footprint)
    (selected : Finset (Fin ((K.jordanContour jordan contains avoids).length + 1)))
    (a b : Plane) (different : a ≠ b) (remainder : Set Plane) (closed : IsClosed remainder)
    (cover : J ⊆ segment ℝ a b ∪ remainder)
    (outside : ∀ i ∈ selected, K.jordanBankPosition jordan contains avoids i ∉ remainder)
    (regular : ∀ i ∈ selected,
      K.HasRegularSectionSlopes ((K.jordanContourVertexEquiv jordan contains avoids) i).val
        (b - a))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    (∑ i ∈ selected, |K.jordanContourTurnError jordan contains avoids i|) ≤ 2 * φ * sin φ := by
  classical
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let Q := K.jordanContour jordan contains avoids
  let pos := K.jordanBankPosition jordan contains avoids
  let bank (i : selected) := Q.cycle.point i.val
  let d := NormedSpace.normalize (b - a)
  have d_ne : b - a ≠ 0 := sub_ne_zero.mpr different.symm
  have unit : ‖d‖ = 1 := NormedSpace.norm_normalize d_ne
  have direction_ne : d ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at unit
    norm_num at unit
  have on_line {x : Plane} (member : x ∈ segment ℝ a b) : ∃ s : ℝ, x = a + s • d := by
    obtain ⟨t, _, position⟩ := (segment_eq_image_lineMap ℝ a b).le member
    refine ⟨t * ‖b - a‖, ?_⟩
    rw [← position, AffineMap.lineMap_apply_module']
    change t • (b - a) + a = a + (t * ‖b - a‖) • NormedSpace.normalize (b - a)
    rw [mul_smul, NormedSpace.norm_smul_normalize, add_comm]
  have local_line (i : selected) : ∀ᶠ x in 𝓝 (pos i.val),
      x ∈ J → ∃ s : ℝ, x = a + s • d := by
    filter_upwards [closed.isOpen_compl.mem_nhds (outside i.val i.property)] with x absent
    intro member
    exact on_line ((cover member).resolve_right absent)
  have point_line (i : selected) : ∃ s : ℝ, pos i.val = a + s • d :=
    (local_line i).self_of_nhds (K.jordanBankPosition_mem_curve jordan contains avoids i.val)
  choose time position using point_line
  have distinct : Function.Injective time := by
    intro i j same
    apply Subtype.ext
    apply K.jordanBankPosition_injective jordan contains avoids
    change pos i.val = pos j.val
    rw [position i, position j, same]
  have rays (i : selected) : ∃ u v : ℝ, u * v < 0 ∧
      Cap.horizontal ((K.folding.restrictFaces U).germDirection (bank i).val) = u • d ∧
      Cap.horizontal ((K.folding.restrictFaces U).germDirection
        (R.boundaryMate Set.univ (bank i)).val) = v • d := by
    apply K.jordan_bank_rays_of_local_line jordan contains avoids (bank i) d direction_ne
    change ∀ᶠ x in 𝓝 (pos i.val), x ∈ J → ∃ s : ℝ, x = pos i.val + s • d
    filter_upwards [local_line i] with x close
    intro member
    obtain ⟨t, exact_line⟩ := close member
    refine ⟨t - time i, ?_⟩
    rw [exact_line, position i]
    module
  choose u v opposite outgoing incoming using rays
  have at_line (i : selected) : a + time i • d ∈ interior K.footprint := by
    rw [← position]
    exact inside (K.jordanBankPosition_mem_curve jordan contains avoids i.val)
  have regular_normalized (i : selected) : K.HasRegularSectionSlopes
      (C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ (bank i))) d := by
    obtain ⟨f, g, slopes, transverse⟩ := regular i.val i.property
    refine ⟨f, g, slopes, transverse.imp_right ?_⟩
    intro h
    change inner ℝ (f - g) (‖b - a‖⁻¹ • (b - a)) ≠ 0
    rw [real_inner_smul_right]
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr d_ne)) h
  have estimate := K.sum_abs_restricted_section_error_le_sin_tilt U bank a d unit time distinct
    position at_line u v opposite outgoing incoming regular_normalized nonnegative small tilt
  have sum_eq : (∑ i : selected, |K.jordanContourTurnError jordan contains avoids i.val|) =
      ∑ i ∈ selected, |K.jordanContourTurnError jordan contains avoids i| :=
    (Finset.sum_subtype selected (by simp)
      (fun i => |K.jordanContourTurnError jordan contains avoids i|)).symm
  change (∑ i : selected, |K.jordanContourTurnError jordan contains avoids i.val|) ≤ _ at estimate
  exact sum_eq ▸ estimate

end Unfoldings.ConvexCap
