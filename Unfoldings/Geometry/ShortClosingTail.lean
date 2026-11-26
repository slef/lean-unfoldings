module

public import Unfoldings.Geometry.ChainLinearGraph
public import Unfoldings.Geometry.Triangle
public import Mathlib.Analysis.Convex.Topology

/-! The tail above a late level in any strict chain coordinate lies in its last segment. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

/-- A late point on the terminal edge can be chosen inside any neighborhood of
the end without choosing coordinates. -/
theorem exists_terminal_segment_point_near (n_pos : 0 < n) {U : Set Plane}
    (opened : IsOpen U) (endpoint : P.vertex (Fin.last n) ∈ U) :
    ∃ d ∈ U, d ∈ openSegment ℝ (P.vertex ⟨n - 1, by omega⟩) (P.vertex (Fin.last n)) := by
  let p := P.vertex ⟨n - 1, by omega⟩
  let q := P.vertex (Fin.last n)
  have closure : q ∈ closure (openSegment ℝ p q) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ p q)
  obtain ⟨d, inside, membership⟩ := mem_closure_iff_nhds.mp closure U (opened.mem_nhds endpoint)
  exact ⟨d, inside, membership⟩

/-- The chain coordinate determines any point after the terminal landmark by
the final subsegment. This also applies after rotating the coordinate. -/
theorem mem_terminal_subsegment_of_coord_ge (n_pos : 0 < n)
    (h : Plane →L[ℝ] ℝ) (progress : ∀ i, 0 < h (P.edge i))
    {d p : Plane} (landmark : d ∈ segment ℝ (P.vertex ⟨n - 1, by omega⟩) (P.vertex (Fin.last n)))
    (member : p ∈ Set.range P.path) (past : h d ≤ h p) :
    p ∈ segment ℝ d (P.vertex (Fin.last n)) := by
  let q := P.vertex (Fin.last n)
  let first := P.vertex ⟨n - 1, by omega⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  have right_eq : j.succ = Fin.last n := by apply Fin.ext; change n - 1 + 1 = n; omega
  have left_eq : P.vertex j.castSucc = first := rfl
  have last_eq : P.vertex j.succ = q := congrArg P.vertex right_eq
  have in_path : segment ℝ first q ⊆ Set.range P.path := by
    intro z hz
    rw [P.path_range]
    right
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change z ∈ Set.range (Path.segment (P.vertex j.castSucc) (P.vertex j.succ))
    rwa [Path.range_segment, left_eq, last_eq]
  have flat (i : Fin n) (zero : h (P.edge i) = 0) : P.edge i = 0 :=
    ((progress i).ne' zero).elim
  let chart := P.linearGraphHomeomorph h (fun i => (progress i).le) flat n_pos
  have before : h p ≤ h q := (chart ⟨p, member⟩).property.2
  have mapped : h p ∈ h '' segment ℝ d q := by
    rw [show h '' segment ℝ d q = segment ℝ (h d) (h q) from
      image_segment ℝ h.toLinearMap.toAffineMap d q, segment_eq_Icc (past.trans before)]
    exact ⟨past, before⟩
  obtain ⟨z, hz, he⟩ := mapped
  have on : z ∈ Set.range P.path :=
    in_path ((convex_segment first q).segment_subset landmark (right_mem_segment ℝ _ _) hz)
  have hpz : p = z := P.path_linear_injOn h (fun i => (progress i).le) flat n_pos member on he.symm
  rwa [hpz]

end Unfoldings.PolygonalChain
