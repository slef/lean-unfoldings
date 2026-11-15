module

public import Unfoldings.Complex.WeightedBoundaryIncidence
public import Unfoldings.Complex.RelativeBankEnumeration
public import Unfoldings.Complex.BoundaryContour
public import Unfoldings.Complex.DiskBoundaryQuotient
public import Unfoldings.Complex.RelativeSeamGeometry

/-! Further original cuts increase old boundary-copy counts by their actual new edge endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  (first : C.BoundaryContour small) (last : C.BoundaryContour large)

include first last in
open Classical in
/-- For weights supported on old boundary vertices, the exact new-copy count equals the
old count plus the actual endpoints of every newly cut original seam. Internal original
vertices and branching are allowed; no copy-multiplicity certificate is assumed. -/
theorem sum_relative_boundary_copy_weights (weight : C.Vertex large → ℝ)
    (zero_internal : ∀ v, ¬ C.IsBoundaryVertex large v → weight v = 0) :
    (∑ w : C.Vertex small, weight (C.vertexForgetCuts inclusion w)) =
      (∑ v : C.Vertex large, weight v) +
        ∑ s : C.RelativeCutSeam small large,
          (weight (C.relativeCutVertex small large s false) +
            weight (C.relativeCutVertex small large s true)) := by
  classical
  let := C.finite_boundaryBank small
  let := C.finite_boundaryBank large
  let := Fintype.ofFinite (C.BoundaryBank small)
  let := Fintype.ofFinite (C.BoundaryBank large)
  let bankWeight (bank : C.BoundaryBank small) : ℝ :=
    weight (C.relativeBoundaryVertex inclusion ((C.boundaryGraph small).left bank)) +
      weight (C.relativeBoundaryVertex inclusion ((C.boundaryGraph small).right bank))
  let oldWeight (bank : C.BoundaryBank large) : ℝ :=
    weight ((C.boundaryGraph large).left bank).val + weight ((C.boundaryGraph large).right bank).val
  let cutWeight (s : C.RelativeCutSeam small large) : ℝ :=
    weight (C.relativeCutVertex small large s false) +
      weight (C.relativeCutVertex small large s true)
  have old_value (bank : C.BoundaryBank large) :
      bankWeight (C.oldBoundaryBank inclusion bank) = oldWeight bank := rfl
  have cut_value (s : C.RelativeCutSeam small large) (side : Bool) :
      bankWeight (C.relativeCutBank small large s side) = cutWeight s := by
    have link := C.relativeCutGraph_bank_link inclusion s side
    rcases link with ⟨first, last⟩ | ⟨first, last⟩
    · change weight _ + weight _ = weight _ + weight _
      rw [first, last]
    · change weight _ + weight _ = weight _ + weight _
      rw [first, last, add_comm]
  have enumeration := (C.relativeBoundaryBankEquiv inclusion).sum_comp bankWeight
  change (∑ a : C.BoundaryBank large ⊕ (C.RelativeCutSeam small large × Bool),
    bankWeight (Sum.elim (C.oldBoundaryBank inclusion)
      (fun p => C.relativeCutBank small large p.1 p.2) a)) = ∑ bank, bankWeight bank at enumeration
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    old_value, cut_value, Fintype.sum_bool, ← two_mul] at enumeration
  rw [← Finset.mul_sum] at enumeration
  have new_zero (w : C.Vertex small) (internal : ¬ C.IsBoundaryVertex small w) :
      weight (C.vertexForgetCuts inclusion w) = 0 := by
    apply zero_internal
    intro old_boundary
    apply internal
    apply (C.vertexPoint_mem_bankBoundary_iff small w).mp
    apply C.bankBoundary_preimage_forgetCuts inclusion
    change C.forgetCuts inclusion (C.vertexPoint small w) ∈ C.bankBoundary large
    rw [← C.vertexPoint_vertexForgetCuts]
    exact (C.vertexPoint_mem_bankBoundary_iff large _).mpr old_boundary
  have new_count := C.sum_boundaryBank_weighted_incidence small
    first.cycle first.closes first.covers
    (fun w => weight (C.vertexForgetCuts inclusion w)) new_zero
  have old_count := C.sum_boundaryBank_weighted_incidence large last.cycle last.closes last.covers
    weight zero_internal
  change (∑ bank, bankWeight bank) = 2 * ∑ w, weight (C.vertexForgetCuts inclusion w) at new_count
  change (∑ bank, oldWeight bank) = 2 * ∑ v, weight v at old_count
  change (∑ bank, oldWeight bank) + 2 * ∑ s, cutWeight s = ∑ bank, bankWeight bank at enumeration
  change (∑ w, weight (C.vertexForgetCuts inclusion w)) = (∑ v, weight v) + ∑ s, cutWeight s
  linarith

end Unfoldings.TriangleComplex
