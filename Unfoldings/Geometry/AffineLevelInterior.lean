module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Function

/-! A cut through a regular side enters each adjacent convex body at the same height. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Every affine value strictly between two values on a full-dimensional
convex set is realized in its interior. -/
theorem exists_interior_point_of_linear_between {S : Set Plane} (convex : Convex ℝ S)
    (inside : (interior S).Nonempty) (height : Plane →L[ℝ] ℝ)
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S)
    {value : ℝ} (lower : height x < value) (upper : value < height y) :
    ∃ q ∈ interior S, height q = value := by
  have dense : closure (interior S) = closure S :=
    convex.closure_interior_eq_closure_of_nonempty_interior inside
  have below : IsOpen {p : Plane | height p < value} :=
    isOpen_lt height.continuous continuous_const
  have above : IsOpen {p : Plane | value < height p} :=
    isOpen_lt continuous_const height.continuous
  have xclose : x ∈ closure (interior S) := dense.symm ▸ subset_closure hx
  have yclose : y ∈ closure (interior S) := dense.symm ▸ subset_closure hy
  obtain ⟨p, hp, p_in⟩ := (mem_closure_iff.mp xclose) _ below lower
  obtain ⟨q, hq, q_in⟩ := (mem_closure_iff.mp yclose) _ above upper
  have image : Convex ℝ (height '' interior S) := convex.interior.linear_image height.toLinearMap
  have exists_value : value ∈ height '' interior S := by
    have segment := image.segment_subset (Set.mem_image_of_mem height p_in)
      (Set.mem_image_of_mem height q_in)
    apply segment
    rw [segment_eq_Icc (hp.trans hq).le]
    exact ⟨hp.le, hq.le⟩
  exact exists_value

end Unfoldings
