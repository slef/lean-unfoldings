module

public import Unfoldings.Geometry.ChainHeightCover
public import Unfoldings.Topology.FiniteMonotoneSelection
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Coordinate order along an exact height graph survives continuous face-chart changes. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n) (G : MonotoneHeightGraph)
  (representation : ∀ j (s : unitInterval),
    G.coordinate ((P.point j s).re + (P.point j s).im) = (P.point j s).re)
  (positive : ∀ j, 0 < (P.edge j).re + (P.edge j).im)

include representation positive

/-- Only the actual chain directions are tested. The affine coordinate need not
be monotone on the surrounding quadrant. -/
theorem heightGraph_affine_monotoneOn (A : ℂ →ᵃ[ℝ] ℝ)
    (increments : ∀ j, 0 ≤ A.linear (P.edge j)) :
    MonotoneOn (fun h => A (G.point h))
      (Set.Ico ((P.vertex 0).re + (P.vertex 0).im)
        ((P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im)) := by
  intro a ha b hb ordered
  by_cases same : a = b
  · rw [same]
  have strict : a < b := lt_of_le_of_ne ordered same
  obtain ⟨j, s, first⟩ := P.heightGraph_point_on_chain G representation positive a ha.1 ha.2
  obtain ⟨k, r, last⟩ := P.heightGraph_point_on_chain G representation positive b hb.1 hb.2
  let height : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap
  have height_order := (P.monotone_linear_vertices_iff height).mpr
    (fun j => (positive j).le)
  have before : Before j s k r := by
    by_contra reversed
    have back : Before k r j s := by
      rcases lt_trichotomy j k with h | h | h
      · exact (reversed (Or.inl h)).elim
      · subst k
        exact Or.inr ⟨rfl, le_of_not_ge (fun h => reversed (Or.inr ⟨rfl, h⟩))⟩
      · exact Or.inl h
    have bound := P.linear_point_le height height_order k j r s back
    rw [← first, ← last] at bound
    change (G.point b).re + (G.point b).im ≤ (G.point a).re + (G.point a).im at bound
    rw [G.point_height, G.point_height] at bound
    exact (not_le_of_gt strict) bound
  let Q : PolygonalChain ℝ n := ⟨fun j => A (P.vertex j)⟩
  have qincrements (j : Fin n) : 0 ≤ (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (Q.edge j) := by
    change 0 ≤ A (P.vertex j.succ) - A (P.vertex j.castSucc)
    have equation : A.linear (P.edge j) =
        A (P.vertex j.succ) - A (P.vertex j.castSucc) := A.linear_apply_vsub _ _
    exact equation ▸ increments j
  have bound := Q.linear_point_le LinearMap.id
    ((Q.monotone_linear_vertices_iff LinearMap.id).mpr qincrements) j k s r before
  have point (j : Fin n) (s : unitInterval) : Q.point j s = A (P.point j s) :=
    (A.apply_lineMap _ _ _).symm
  change Q.point j s ≤ Q.point k r at bound
  rwa [point, point, ← first, ← last] at bound

/-- A visible trace may switch charts arbitrarily, including at branch vertices.
Continuity and nonnegative chart increments on the actual edges suffice. -/
theorem heightGraph_finite_selection_order {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℝ) (continuous : ∀ i, Continuous (A i))
    (increments : ∀ i j, 0 ≤ (A i).linear (P.edge j))
    {value : ℂ → ℝ} (value_continuous : Continuous value)
    {a b : ℝ} (start : (P.vertex 0).re + (P.vertex 0).im ≤ a)
    (ordered : a ≤ b)
    (finish : b < (P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im)
    (selection : ∀ h ∈ Set.Icc a b, ∃ i, value (G.point h) = A i (G.point h)) :
    value (G.point a) ≤ value (G.point b) := by
  let h := fun s : unitInterval => AffineMap.lineMap a b (s : ℝ)
  have bounds (s : unitInterval) : h s ∈ Set.Icc a b :=
    (convex_Icc a b).lineMap_mem ⟨le_rfl, ordered⟩ ⟨ordered, le_rfl⟩ s.property
  have hcontinuous : Continuous h :=
    (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] ℝ).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hmonotone : Monotone h := by
    intro s r before
    dsimp only [h]
    simp only [AffineMap.lineMap_apply_module', smul_eq_mul]
    nlinarith [sub_nonneg.mpr ordered, sub_nonneg.mpr (show (s : ℝ) ≤ r from before)]
  have path_continuous := G.point_continuous.comp hcontinuous
  have bound := finite_monotone_selection_endpoints
    (fun i s => A i (G.point (h s)))
    (fun i => (continuous i).comp path_continuous)
    (fun i s r before => P.heightGraph_affine_monotoneOn G representation positive
      (A i) (increments i) ⟨start.trans (bounds s).1, (bounds s).2.trans_lt finish⟩
      ⟨start.trans (bounds r).1, (bounds r).2.trans_lt finish⟩ (hmonotone before))
    (fun s => value (G.point (h s))) (value_continuous.comp path_continuous)
    (fun s => selection (h s) (bounds s))
  change value (G.point (AffineMap.lineMap a b (0 : ℝ))) ≤
    value (G.point (AffineMap.lineMap a b (1 : ℝ))) at bound
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using bound

end Unfoldings.PolygonalChain
