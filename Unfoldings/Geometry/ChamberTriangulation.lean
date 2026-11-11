module

public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.CompactHalfplanes
public import Unfoldings.Geometry.ConvexPolygonPartition

/-! Triangulating every compact chamber of a prescribed finite affine arrangement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineArrangement

universe u

variable {ι : Type u} [Finite ι] (equation : ι → Plane →ᵃ[ℝ] ℝ)

omit [Finite ι] in
/-- A weak sign at a strict chamber point determines that sign throughout its closure. -/
theorem closedChamber_nonnegative_of_chamber_nonnegative (signs : ι → Bool)
    {p q : Plane} (first : p ∈ chamber equation signs) (last : q ∈ closedChamber equation signs)
    (i : ι) (nonnegative : 0 ≤ equation i p) : 0 ≤ equation i q := by
  have strict := first i
  have weak := last i
  cases equal : signs i
  · have negative : equation i p < 0 := by simpa [signed_apply, equal] using strict
    exact (not_lt_of_ge nonnegative negative).elim
  · simpa only [signed_apply, equal, ite_eq_left] using weak

theorem exists_compact_chamber_triangle_partition
    (proper : ∀ i, equation i ≠ 0) (signs : ι → Bool)
    (nonempty : (chamber equation signs).Nonempty)
    (compact : IsCompact (closedChamber equation signs)) :
    ∃ (I : Type) (_ : Finite I) (triangle : I → Triangle),
      closedChamber equation signs = ⋃ i, (triangle i).carrier ∧
      Pairwise (fun i j =>
        Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)) := by
  let inequalities (i : ι) := -signed (equation i) (signs i)
  have proper_inequalities (i : ι) : inequalities i ≠ 0 := by
    apply neg_ne_zero.mpr
    cases equal : signs i
    · simpa [signed, equal] using proper i
    · simpa [signed, equal] using proper i
  have region : closedChamber equation signs = nonpositiveRegion inequalities := by
    ext p
    simp only [closedChamber, nonpositiveRegion, inequalities, Set.mem_ofPred_eq,
      AffineMap.coe_neg, Pi.neg_apply, neg_nonpos]
  obtain ⟨edges, finite, boundary⟩ := exists_finite_nonpositive_boundary_segments inequalities
    proper_inequalities (region ▸ compact)
  rw [← region] at boundary
  exact exists_finite_triangle_partition_of_convex_polygon compact
    (convex_closedChamber equation signs)
    (by rwa [interior_closedChamber equation signs nonempty]) edges finite boundary

/-- An exact triangle partition aligned to every line in the supplied arrangement. -/
theorem exists_finite_chamber_triangle_partition (proper : ∀ i, equation i ≠ 0)
    {S : Set Plane} (compact : IsCompact S) (regular_closed : closure (interior S) = S)
    (support : ∀ x ∈ frontier S, ∃ i, equation i x = 0) :
    ∃ (I : Type u) (_ : Finite I) (triangle : I → Triangle) (signs : I → ι → Bool),
      S = ⋃ i, (triangle i).carrier ∧
      Pairwise (fun i j =>
        Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)) ∧
      ∀ i, (chamber equation (signs i)).Nonempty ∧
        (triangle i).carrier ⊆ closedChamber equation (signs i) := by
  classical
  obtain ⟨active, finite_active, properties, covers⟩ :=
    exists_finite_closed_chamber_cover equation proper compact regular_closed support
  let := finite_active.to_subtype
  have partition (a : active) := exists_compact_chamber_triangle_partition equation proper a.val
    (properties a.val a.property).1 (properties a.val a.property).2.2
  choose Index finite triangle local_cover local_separated using partition
  let finite_part (a : active) : Finite (Index a) := finite a
  let I := (a : active) × Index a
  let result (i : I) := triangle i.1 i.2
  have contained (i : I) : (result i).carrier ⊆ closedChamber equation i.1.val := by
    rw [local_cover i.1]
    exact Set.subset_iUnion (fun j => (triangle i.1 j).carrier) i.2
  refine ⟨I, inferInstance, result, fun i => i.1.val, ?_, ?_, ?_⟩
  · ext p
    constructor
    · intro member
      obtain ⟨a, present, inside⟩ := Set.mem_iUnion₂.mp (covers ▸ member)
      rw [local_cover ⟨a, present⟩] at inside
      obtain ⟨i, member⟩ := Set.mem_iUnion.mp inside
      exact Set.mem_iUnion.mpr ⟨⟨⟨a, present⟩, i⟩, member⟩
    · intro member
      obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
      rw [covers]
      exact Set.mem_iUnion₂.mpr ⟨i.1.val, i.1.property, contained i member⟩
  · intro i j different
    by_cases same : i.1 = j.1
    · obtain ⟨a, i⟩ := i
      obtain ⟨b, j⟩ := j
      change a = b at same
      subst b
      exact local_separated a (fun equal => different (congrArg (Sigma.mk a) equal))
    · have disjoint : Disjoint (interior (closedChamber equation i.1.val))
          (interior (closedChamber equation j.1.val)) := by
        rw [interior_closedChamber equation i.1.val (properties i.1.val i.1.property).1,
          interior_closedChamber equation j.1.val (properties j.1.val j.1.property).1]
        exact Set.disjoint_left.mpr (fun _ first last =>
          same (Subtype.ext (chamber_signs_unique equation first last)))
      exact disjoint.mono (interior_mono (contained i)) (interior_mono (contained j))
  · intro i
    exact ⟨(properties i.1.val i.1.property).1, contained i⟩

end Unfoldings.AffineArrangement
