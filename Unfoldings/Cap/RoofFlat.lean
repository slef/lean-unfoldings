module

public import Unfoldings.Cap.RoofLevels
public import Unfoldings.Cap.Flat

/-! Geometric cap input either gives an already unfolded flat cap or a positive roof height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Zero roof height on the footprint makes every whole original affine face horizontal. -/
theorem face_height_zero_of_zero_roof
    (zero : ∀ p ∈ K.footprint, K.roofHeight p = 0) (f : Face) (x : Plane) :
    K.folding.place f x 2 = 0 := by
  let height : Plane →ᵃ[ℝ] ℝ :=
    (EuclideanSpace.proj 2).toLinearMap.toAffineMap.comp (K.folding.place f).toAffineMap
  have equal : height = AffineMap.const ℝ Plane 0 := by
    apply (C.triangle f).affine_ext
    intro i
    have member : K.projectFace f ((C.triangle f).vertex i) ∈ K.footprint :=
      ⟨K.folding.place f ((C.triangle f).vertex i),
        Set.mem_iUnion.mpr ⟨f, ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i, rfl⟩⟩, rfl⟩
    have value := zero _ member
    rw [K.roofHeight_face f ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i⟩] at value
    exact value
  exact congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A x) equal

theorem flat_of_zero_roof (zero : ∀ p ∈ K.footprint, K.roofHeight p = 0) : K.TiltBound 0 := by
  intro f
  rw [Real.cos_zero]
  obtain ⟨x, first⟩ := K.projectFace_surjective f (Cap.horizontal (K.normal f))
  obtain ⟨y, last⟩ := K.projectFace_surjective f 0
  have tangent := K.normal_tangent_chord f x y
  rw [Cap.horizontal_inner, map_sub] at tangent
  change inner ℝ (Cap.horizontal (K.normal f)) (K.projectFace f x - K.projectFace f y) +
    K.normal f 2 * (K.folding.place f x 2 - K.folding.place f y 2) = 0 at tangent
  rw [first, last, K.face_height_zero_of_zero_roof zero, K.face_height_zero_of_zero_roof zero,
    sub_zero, sub_self, mul_zero, add_zero, real_inner_self_eq_norm_sq] at tangent
  have horizontal_zero : ‖Cap.horizontal (K.normal f)‖ = 0 := (sq_eq_zero_iff).mp tangent
  have identity := Cap.horizontal_norm_sq (K.normal f)
  rw [K.normal_unit f, horizontal_zero] at identity
  nlinarith [K.normal_upward f]

/-- Bounded clips need a positive height, which exists unless the flat theorem applies. -/
theorem flat_or_positive_roof :
    K.TiltBound 0 ∨ ∃ p ∈ K.footprint, 0 < K.roofHeight p := by
  classical
  by_cases positive : ∃ p ∈ K.footprint, 0 < K.roofHeight p
  · exact Or.inr positive
  · left
    apply K.flat_of_zero_roof
    intro p member
    exact le_antisymm (le_of_not_gt (fun h => positive ⟨p, member, h⟩))
      (K.roofHeight_nonneg_of_mem member)

end Unfoldings.ConvexCap
