module

public import Unfoldings.Geometry.MeshHalfplaneProgress
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Original incident edges approximate any requested direction by half the corner bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology
open scoped NNReal

theorem exists_mesh_direction_edge {Face : Type*} [Finite Face] (triangle : Face → Triangle)
    (region : Set Plane) (cover : region ⊆ ⋃ f, (triangle f).carrier) (center : Plane)
    (inside : center ∈ interior region)
    (corner : ∀ f, center ∈ (triangle f).carrier → ∃ i, (triangle f).vertex i = center)
    {β : ℝ} (angles : ∀ f i, (triangle f).cornerAngle i ≤ 2 * β)
    (direction : Plane) (nonzero : direction ≠ 0) :
    ∃ f i, (triangle f).vertex i = center ∧
      (InnerProductGeometry.angle direction ((triangle f).vertex (Triangle.next i) - center) ≤ β ∨
        InnerProductGeometry.angle direction
          ((triangle f).vertex (Triangle.next (Triangle.next i)) - center) ≤ β) := by
  have star := eventually_piece_contains_center (fun f => (triangle f).carrier)
    (fun f => (triangle f).compact_carrier.isClosed) center
  have near : {p | p ∈ region ∧ ∀ f, p ∈ (triangle f).carrier →
      center ∈ (triangle f).carrier} ∈ 𝓝 center := by
    filter_upwards [star, isOpen_interior.mem_nhds inside] with p hp interior
    exact ⟨interior_subset interior, hp⟩
  obtain ⟨t, tpos, present, star⟩ := exists_positive_ray_mem center direction _ near
  obtain ⟨f, in_face⟩ := Set.mem_iUnion.mp (cover present)
  obtain ⟨i, vertex⟩ := corner f (star f in_face)
  let u := (triangle f).vertex (Triangle.next i) - center
  let v := (triangle f).vertex (Triangle.next (Triangle.next i)) - center
  let a := (triangle f).coord (Triangle.next i) (center + t • direction)
  let b := (triangle f).coord (Triangle.next (Triangle.next i)) (center + t • direction)
  have coefficients := (triangle f).carrier_subset_cornerWedge i in_face
  have combination := (triangle f).reconstruct_corner i (center + t • direction)
  have expression : t • direction = a • u + b • v := by
    have equation := congrArg (fun p : Plane => p - center) combination
    simpa only [Triangle.cornerCombination, vertex, add_sub_cancel_right,
      add_sub_cancel_left] using equation.symm
  let acoef : ℝ≥0 := ⟨a, coefficients.1⟩
  let bt : ℝ≥0 := ⟨b, coefficients.2⟩
  let tt : ℝ≥0 := ⟨t, tpos.le⟩
  have ttne : tt ≠ 0 := by
    intro zero
    have equal := congrArg (fun r : ℝ≥0 => (r : ℝ)) zero
    exact tpos.ne' equal
  have ray_in_span : tt • direction ∈ Submodule.span ℝ≥0 {u, v} := by
    rw [Submodule.mem_span_pair]
    exact ⟨acoef, bt, expression.symm⟩
  have in_span : direction ∈ Submodule.span ℝ≥0 {u, v} :=
    (Submodule.smul_mem_iff _ ttne).mp ray_in_span
  have split := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span nonzero in_span
  have bound : InnerProductGeometry.angle u v ≤ 2 * β := by
    have angle := angles f i
    change InnerProductGeometry.angle
      ((triangle f).vertex (Triangle.next i) - (triangle f).vertex i)
      ((triangle f).vertex (Triangle.next (Triangle.next i)) - (triangle f).vertex i) ≤
        2 * β at angle
    simpa only [vertex] using angle
  refine ⟨f, i, vertex, ?_⟩
  change InnerProductGeometry.angle direction u ≤ β ∨ InnerProductGeometry.angle direction v ≤ β
  rw [split] at bound
  have comm := InnerProductGeometry.angle_comm u direction
  by_cases first : InnerProductGeometry.angle direction u ≤ β
  · exact Or.inl first
  · exact Or.inr (by linarith)

end Unfoldings
