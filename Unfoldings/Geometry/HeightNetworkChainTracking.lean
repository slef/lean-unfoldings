module

public import Unfoldings.Geometry.HeightSegmentNetwork
public import Unfoldings.Geometry.ChainHeightGraph
public import Unfoldings.Geometry.ChainHeightCover

/-! A monotone fine chain and a covered tail with the same start follow the same network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.HeightSegmentNetwork

variable {ι : Type*} [Finite ι] (N : HeightSegmentNetwork ι)

/-- Forward uniqueness identifies a represented tail point with an actual whole-edge
point of any covered monotone refinement starting there. No combinatorial matching
between coarse edges and refinement edges is supplied. -/
theorem heightGraph_point_on_covered_chain {n : ℕ} (P : PolygonalChain ℂ n)
    (directions : ∀ j, 0 ≤ (P.edge j).re ∧ 0 ≤ (P.edge j).im)
    (positive : ∀ j, 0 < (P.edge j).re + (P.edge j).im)
    (chain_cover : ∀ j s, P.point j s ∈ N.carrier)
    (H : MonotoneHeightGraph) {b : ℝ}
    (tail_cover : ∀ h ∈ Set.Icc ((P.vertex 0).re + (P.vertex 0).im) b,
      H.point h ∈ N.carrier)
    (initial : H.coordinate ((P.vertex 0).re + (P.vertex 0).im) = (P.vertex 0).re)
    (finish : b < (P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im)
    {h : ℝ} (member : h ∈ Set.Icc ((P.vertex 0).re + (P.vertex 0).im) b) :
    ∃ j : Fin n, ∃ s : unitInterval, H.point h = P.point j s := by
  obtain ⟨G, vertices, pieces⟩ := P.exists_heightGraph directions positive
  have graph_cover : ∀ h ∈ Set.Icc ((P.vertex 0).re + (P.vertex 0).im) b,
      G.point h ∈ N.carrier := by
    intro h member
    obtain ⟨j, s, value⟩ := P.heightGraph_point_on_chain G pieces positive h member.1
      (member.2.trans_lt finish)
    rw [value]
    exact chain_cover j s
  have coalesces := N.graphs_coalesce G H graph_cover tail_cover
  have equal := coalesces ((P.vertex 0).re + (P.vertex 0).im)
    ⟨le_rfl, member.1.trans member.2⟩ ((vertices 0).trans initial.symm) h member
  have point : H.point h = G.point h := by
    apply Complex.ext
    · exact equal.symm
    · change h - H.coordinate h = h - G.coordinate h
      rw [equal]
  obtain ⟨j, s, value⟩ := P.heightGraph_point_on_chain G pieces positive h member.1
    (member.2.trans_lt finish)
  exact ⟨j, s, point.trans value⟩

/-- The same tracking result in arbitrary affine coordinates, retaining the actual
physical chain point rather than only an abstract point of the transformed chain. -/
theorem heightGraph_point_on_affine_covered_chain {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (A : E →ᵃ[ℝ] ℂ) (P : PolygonalChain E n)
    (directions : ∀ j, 0 ≤ (A.linear (P.edge j)).re ∧ 0 ≤ (A.linear (P.edge j)).im)
    (positive : ∀ j, 0 < (A.linear (P.edge j)).re + (A.linear (P.edge j)).im)
    (chain_cover : ∀ j s, A (P.point j s) ∈ N.carrier)
    (H : MonotoneHeightGraph) {b : ℝ}
    (tail_cover : ∀ h ∈ Set.Icc ((A (P.vertex 0)).re + (A (P.vertex 0)).im) b,
      H.point h ∈ N.carrier)
    (initial : H.coordinate ((A (P.vertex 0)).re + (A (P.vertex 0)).im) = (A (P.vertex 0)).re)
    (finish : b < (A (P.vertex (Fin.last n))).re + (A (P.vertex (Fin.last n))).im)
    {h : ℝ} (member : h ∈ Set.Icc ((A (P.vertex 0)).re + (A (P.vertex 0)).im) b) :
    ∃ j : Fin n, ∃ s : unitInterval, H.point h = A (P.point j s) := by
  let Q : PolygonalChain ℂ n := ⟨fun j => A (P.vertex j)⟩
  have edge (j : Fin n) : Q.edge j = A.linear (P.edge j) :=
    (A.linear_apply_vsub (P.vertex j.succ) (P.vertex j.castSucc)).symm
  have point (j : Fin n) (s : unitInterval) : Q.point j s = A (P.point j s) :=
    (A.apply_lineMap (P.vertex j.castSucc) (P.vertex j.succ) (s : ℝ)).symm
  obtain ⟨j, s, value⟩ := N.heightGraph_point_on_covered_chain Q
    (fun j => by rw [edge]; exact directions j) (fun j => by rw [edge]; exact positive j)
    (fun j s => by rw [point]; exact chain_cover j s) H tail_cover initial finish member
  exact ⟨j, s, value.trans (point j s)⟩

end Unfoldings.HeightSegmentNetwork
