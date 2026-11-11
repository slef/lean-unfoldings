module

public import Unfoldings.Cap.SectionAngles
public import Unfoldings.Topology.FiniteIntervalCover
public import Mathlib.Topology.Order.Compact

/-!
# Constructed finite original-face traces of cap sections

Every straight projected segment in the convex footprint has a finite strictly
ordered partition into whole pieces contained in original projected triangles.
The original face labels and the actual concave roof agree on each piece.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Actual projected-face membership identifies the roof with that face's supporting plane. -/
theorem roofHeight_eq_supportHeight_of_mem (f : Face) {p : Plane}
    (inside : p ∈ (K.projectedTriangle f).carrier) : K.roofHeight p = K.supportHeight f p := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at inside
  obtain ⟨x, carrier, rfl⟩ := inside
  exact (K.roofHeight_face f ⟨x, carrier⟩).trans (K.supportHeight_face f x).symm

/-- Construct the face trace from the actual finite convex cover. -/
theorem exists_section_face_partition {p q : Plane} (first : p ∈ K.footprint)
    (last : q ∈ K.footprint) :
    ∃ n : ℕ, 0 < n ∧ ∃ time : Fin (n + 1) → unitInterval,
      StrictMono time ∧ time 0 = 0 ∧ time (Fin.last n) = 1 ∧
      ∃ face : Fin n → Face, ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ),
        AffineMap.lineMap p q (t : ℝ) ∈ (K.projectedTriangle (face i)).carrier := by
  classical
  let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap p q
  let times (f : Face) : Set ℝ :=
    Set.Icc 0 1 ∩ line ⁻¹' (K.projectedTriangle f).carrier
  have closed (f : Face) : IsClosed (times f) :=
    isClosed_Icc.inter ((K.projectedTriangle f).compact_carrier.isClosed.preimage
      line.continuous_of_finiteDimensional)
  have compact (f : Face) : IsCompact (times f) :=
    isCompact_Icc.of_isClosed_subset (closed f) (fun _ member => member.1)
  have convex (f : Face) : Convex ℝ (times f) :=
    (convex_Icc (0 : ℝ) 1).inter ((K.projectedTriangle f).convex_carrier.affine_preimage line)
  let Active := {f : Face // (times f).Nonempty}
  have intervals (f : Active) : times f.val = Set.Icc (sInf (times f.val)) (sSup (times f.val)) :=
    eq_Icc_of_connected_compact ⟨f.property, (convex f.val).isPreconnected⟩ (compact f.val)
  let lower (f : Active) : unitInterval :=
    ⟨sInf (times f.val), ((compact f.val).sInf_mem f.property).1⟩
  let upper (f : Active) : unitInterval :=
    ⟨sSup (times f.val), ((compact f.val).sSup_mem f.property).1⟩
  have cover (t : unitInterval) : ∃ f : Active, lower f ≤ t ∧ t ≤ upper f := by
    have footprint : line (t : ℝ) ∈ K.footprint :=
      K.convex_projection.lineMap_mem first last t.property
    obtain ⟨f, member⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset footprint)
    have at_t : (t : ℝ) ∈ times f := ⟨t.property, member⟩
    let active : Active := ⟨f, ⟨t, at_t⟩⟩
    exact ⟨active, (Set.ext_iff.mp (intervals active) (t : ℝ)).mp at_t⟩
  obtain ⟨n, _bound, time, increasing, start, finish, face, contained⟩ :=
    exists_finite_interval_subdivision lower upper cover
  have positive : 0 < n := by
    by_contra zero
    have equal : Fin.last n = 0 := Fin.ext (Nat.eq_zero_of_not_pos zero)
    have impossible := finish
    rw [equal, start] at impossible
    exact zero_ne_one impossible
  refine ⟨n, positive, time, increasing, start, finish, fun i => (face i).val, ?_⟩
  intro i t inside
  have in_interval := contained i inside
  have member : (t : ℝ) ∈ times (face i).val :=
    (Set.ext_iff.mp (intervals (face i)) (t : ℝ)).mpr in_interval
  exact member.2

end Unfoldings.ConvexCap
