module

public import Unfoldings.Complex.RelativeBoundaryCopyCount
public import Unfoldings.Complex.AngleCutSums

/-! One new original seam splits an old boundary endpoint into exactly two angle copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  (first : C.BoundaryContour small) (last : C.BoundaryContour large)

include first last in
open Classical in
/-- A single new seam has exactly two copies above its old boundary endpoint, provided
its other old endpoint differs. Both copies and their angle sum are derived intrinsically. -/
theorem exists_two_boundary_copies_of_single_cut (s : C.RelativeCutSeam small large)
    (single : small = large \ {s.val}) (vertex : C.Vertex large)
    (boundary : C.IsBoundaryVertex large vertex)
    (endpoint :
      (C.relativeCutVertex small large s false = vertex ∧
        C.relativeCutVertex small large s true ≠ vertex) ∨
      (C.relativeCutVertex small large s true = vertex ∧
        C.relativeCutVertex small large s false ≠ vertex)) :
    ∃ a b : C.Vertex small, a ≠ b ∧
      (∀ w, C.vertexForgetCuts inclusion w = vertex ↔ w = a ∨ w = b) ∧
      C.totalAngle small a + C.totalAngle small b = C.totalAngle large vertex := by
  classical
  let weight (v : C.Vertex large) : ℝ := if v = vertex then 1 else 0
  have zero_internal (v : C.Vertex large) (internal : ¬ C.IsBoundaryVertex large v) :
      weight v = 0 := by
    have different : v ≠ vertex := by rintro rfl; exact internal boundary
    exact ite_eq_right different
  have only (t : C.RelativeCutSeam small large) : t = s := by
    apply Subtype.ext
    by_contra different
    apply t.property.2
    apply (Set.ext_iff.mp single t.val).mpr
    exact ⟨t.property.1, by simpa only [Set.mem_singleton_iff] using different⟩
  have one_cut : (∑ t : C.RelativeCutSeam small large,
      (weight (C.relativeCutVertex small large t false) +
        weight (C.relativeCutVertex small large t true))) = 1 := by
    rw [Finset.sum_eq_single s]
    · rcases endpoint with ⟨at_first, not_last⟩ | ⟨at_last, not_first⟩
      · simp only [weight, at_first, ite_true, ite_eq_right not_last, add_zero]
      · simp only [weight, at_last, ite_true, ite_eq_right not_first, zero_add]
    · intro t _ different
      exact (different (only t)).elim
    · intro absent
      exact (absent (Finset.mem_univ s)).elim
  have count := C.sum_relative_boundary_copy_weights inclusion first last weight zero_internal
  have old_count : (∑ v : C.Vertex large, weight v) = 1 := by simp [weight]
  rw [old_count, one_cut] at count
  have cardinal : (Finset.univ.filter
      (fun w : C.Vertex small => C.vertexForgetCuts inclusion w = vertex)).card = 2 := by
    have numeric : ((Finset.univ.filter
        (fun w : C.Vertex small => C.vertexForgetCuts inclusion w = vertex)).card : ℝ) = 2 := by
      simpa only [weight, Finset.sum_boole, one_add_one_eq_two] using count
    exact_mod_cast numeric
  obtain ⟨a, b, distinct, all⟩ := Finset.card_eq_two.mp cardinal
  have fiber (w : C.Vertex small) :
      C.vertexForgetCuts inclusion w = vertex ↔ w = a ∨ w = b := by
    have membership := Finset.ext_iff.mp all w
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] using membership
  have angles := C.sum_totalAngle_vertexForgetCuts inclusion vertex
  rw [← Finset.sum_filter, all] at angles
  refine ⟨a, b, distinct, fiber, ?_⟩
  simpa only [Finset.sum_pair distinct] using angles

end Unfoldings.TriangleComplex
