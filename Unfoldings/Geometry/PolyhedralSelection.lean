module

public import Unfoldings.Geometry.FiniteAffineSelection

/-!
# Finite polyhedral partitions for continuous affine selections

Refine a boundary arrangement by affine coincidence equations and by every
candidate domain inequality. On each resulting chamber the selected map is
constant and every applicable domain inequality keeps its sign. Continuity
extends both conclusions to the closed polyhedral piece.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open AffineArrangement

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι κ : Type*} [Finite ι] [Finite κ]

theorem exists_polyhedral_selection_cover {s : Set E} (compact : IsCompact s)
    (regular_closed : closure (interior s) = s)
    (boundary_equations : Set (E →ᵃ[ℝ] ℝ)) (finite_boundary : boundary_equations.Finite)
    (boundary_nonzero : ∀ l ∈ boundary_equations, l ≠ 0)
    (boundary_support : ∀ x ∈ frontier s, ∃ l ∈ boundary_equations, l x = 0)
    (maps : ι → E →ᵃ[ℝ] V) (inequalities : ι → κ → E →ᵃ[ℝ] ℝ)
    (inequalities_nonzero : ∀ i k, inequalities i k ≠ 0)
    (value : s → V) (continuous_value : Continuous value)
    (selects : ∀ x : s, ∃ i, value x = maps i x.val ∧ ∀ k, 0 ≤ inequalities i k x.val) :
    ∃ L : Set (E →ᵃ[ℝ] ℝ), L.Finite ∧ (∀ l ∈ L, l ≠ 0) ∧
      ∃ S : Set (L → Bool), S.Finite ∧
        (∀ signs ∈ S, IsCompact (closedChamber (fun l : L => l.val) signs) ∧
          (interior (closedChamber (fun l : L => l.val) signs)).Nonempty ∧
          closedChamber (fun l : L => l.val) signs ⊆ s ∧
          ∃ i, ∀ x : s, x.val ∈ closedChamber (fun l : L => l.val) signs →
            value x = maps i x.val ∧ ∀ k, 0 ≤ inequalities i k x.val) ∧
        S.Pairwise (fun a b => Disjoint
          (interior (closedChamber (fun l : L => l.val) a))
          (interior (closedChamber (fun l : L => l.val) b))) ∧
        s = ⋃ signs ∈ S, closedChamber (fun l : L => l.val) signs := by
  classical
  obtain ⟨D, finite_D, nonzero_D, coincidences⟩ := exists_finite_affine_coincidence_equations maps
  let L := boundary_equations ∪ D ∪ Set.range (fun p : ι × κ => inequalities p.1 p.2)
  have finite_L : L.Finite := (finite_boundary.union finite_D).union (Set.finite_range _)
  have nonzero_L : ∀ l ∈ L, l ≠ 0 := by
    intro l member
    rcases member with (hb | hd) | ⟨p, rfl⟩
    · exact boundary_nonzero l hb
    · exact nonzero_D l hd
    · exact inequalities_nonzero p.1 p.2
  let := finite_L.fintype
  let equations (l : L) := l.val
  have boundary : ∀ x ∈ frontier s, ∃ l : L, equations l x = 0 := by
    intro x hx
    obtain ⟨l, hl, zero⟩ := boundary_support x hx
    exact ⟨⟨l, Or.inl (Or.inl hl)⟩, zero⟩
  obtain ⟨S, finite_S, pieces, cover⟩ := exists_finite_closed_chamber_cover equations
    (fun l => nonzero_L l.val l.property) compact regular_closed boundary
  refine ⟨L, finite_L, nonzero_L, S, finite_S, ?_, ?_, cover⟩
  · intro signs member
    obtain ⟨nonempty, inside, compact_piece⟩ := pieces signs member
    have closed_inside : closedChamber equations signs ⊆ s := by
      rw [← closure_chamber equations signs nonempty]
      exact closure_minimal (inside.trans interior_subset) compact.isClosed
    have interior_nonempty : (interior (closedChamber equations signs)).Nonempty := by
      rwa [interior_closedChamber equations signs nonempty]
    refine ⟨compact_piece, interior_nonempty, closed_inside, ?_⟩
    let U := chamber equations signs
    let lift_open (x : U) : s := ⟨x.val, interior_subset (inside x.property)⟩
    have continuous_open : Continuous lift_open := continuous_subtype_val.subtype_mk _
    let := Subtype.connectedSpace ⟨nonempty, (convex_chamber equations signs).isPreconnected⟩
    have separated : ∀ x : U, ∀ i j, maps i ≠ maps j → maps i x.val ≠ maps j x.val := by
      intro x i j different equal
      obtain ⟨l, hl, zero⟩ := coincidences i j different x.val equal
      exact chamber_avoids_zero equations signs x.property ⟨l, Or.inl (Or.inr hl)⟩ zero
    obtain ⟨i, agrees⟩ := finite_affine_selection_constant maps
      (fun x : U => x.val) continuous_subtype_val (value ∘ lift_open)
      (continuous_value.comp continuous_open)
      (fun x => (selects (lift_open x)).imp (fun j hj => hj.1)) separated
    obtain ⟨center, center_member⟩ := nonempty
    let c : U := ⟨center, center_member⟩
    obtain ⟨j, at_center, feasible⟩ := selects (lift_open c)
    have maps_equal : maps i = maps j := by
      by_contra different
      exact separated c i j different ((agrees c).symm.trans at_center)
    have open_formula (x : U) : value (lift_open x) = maps j x.val := by
      have equal := agrees x
      change value (lift_open x) = maps i x.val at equal
      rwa [maps_equal] at equal
    have open_feasible (x : U) (k : κ) : 0 ≤ inequalities j k x.val := by
      let l : L := ⟨inequalities j k, Or.inr ⟨(j, k), rfl⟩⟩
      exact (chamber_positive_of_nonnegative equations signs center_member x.property l
        (feasible k)).le
    let Q := closedChamber equations signs
    let lift_closed (x : Q) : s := ⟨x.val, closed_inside x.property⟩
    have continuous_closed : Continuous lift_closed := continuous_subtype_val.subtype_mk _
    have included : U ⊆ Q := fun _ hx k => (hx k).le
    have dense : DenseRange (Set.inclusion included) := by
      apply (denseRange_inclusion_iff included).mpr
      rw [closure_chamber equations signs ⟨center, center_member⟩]
    have closed_formula : IsClosed {x : Q | value (lift_closed x) = maps j x.val ∧
        ∀ k, 0 ≤ inequalities j k x.val} := by
      have closed_equal : IsClosed {x : Q | value (lift_closed x) = maps j x.val} :=
        isClosed_eq (continuous_value.comp continuous_closed)
          ((maps j).continuous_of_finiteDimensional.comp continuous_subtype_val)
      have closed_inequalities : IsClosed (⋂ k, {x : Q | 0 ≤ inequalities j k x.val}) :=
        isClosed_iInter (fun k => isClosed_le
          (show Continuous (fun _ : Q => (0 : ℝ)) from continuous_const)
          ((inequalities j k).continuous_of_finiteDimensional.comp continuous_subtype_val))
      have equal : {x : Q | ∀ k, 0 ≤ inequalities j k x.val} =
          ⋂ k, {x : Q | 0 ≤ inequalities j k x.val} := by ext; simp
      have closed_feasible : IsClosed {x : Q | ∀ k, 0 ≤ inequalities j k x.val} := by
        rw [equal]
        exact closed_inequalities
      exact closed_equal.inter closed_feasible
    have all_formula (x : Q) : value (lift_closed x) = maps j x.val ∧
        ∀ k, 0 ≤ inequalities j k x.val :=
      dense.induction_on x closed_formula (fun y => ⟨open_formula y, open_feasible y⟩)
    exact ⟨j, fun x hx => all_formula ⟨x.val, hx⟩⟩
  · intro a ha b hb different
    rw [interior_closedChamber equations a (pieces a ha).1,
      interior_closedChamber equations b (pieces b hb).1]
    exact Set.disjoint_left.mpr (fun _ hx hy => different (chamber_signs_unique equations hx hy))

end Unfoldings
