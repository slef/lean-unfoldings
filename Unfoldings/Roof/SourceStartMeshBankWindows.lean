module

public import Unfoldings.Roof.SpatialMeshBankWindows
public import Unfoldings.Roof.ProjectedBankDirections
public import Unfoldings.Geometry.SourceRayWindowContinuity

/-! Uniform physical comparisons include a complete bank that begins at its original source. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

local instance sourceStartWindowsIndexFintype {I : Type u} [Fintype I] [Nonempty I]
    {family : I → SpatialPlane} {Z : ℝ} (T : Triangulation family Z) : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

open Classical in
/-- One tilt controls every source-starting bank, including windows on its actual first edge. -/
theorem exists_uniform_spatial_mesh_sourceStart_bank_windows {η : ℝ} (error_positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {I : Type u} [Fintype I] [Nonempty I] (family : I → SpatialPlane) {Z : ℝ}
        (T : Triangulation family Z) (conforming : TriangleFamily.Conforming T.projectedTriangle)
        (inside : (interior (clip family Z)).Nonempty),
        (∀ i, Real.cos φ ≤ (family i).normal 2) →
        ∀ (retain : Set T.pairedComplex.Seam) {m : ℕ}
          (full : (T.pairedComplex.boundarySystem retain).Chain m),
          let P := T.pairedFolding.projectedBoundaryChain full
          P.RadialFrom (P.vertex 0) 0 →
          ∀ {γ : ℝ}, 0 < γ →
          (∀ i : Fin (m + 1), γ * (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
            inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i)) →
          (∀ j, Cap.horizontal (T.pairedFolding.boundaryPosition (full.point j)) ∈
            interior (clip family Z)) →
          (T.roof conforming inside).SupportedBankWindowComparisons φ η retain full
            (P.vertex 0) := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_spatial_mesh_bank_windows.{u} error_positive
  refine ⟨φ, bounds, ?_⟩
  intro I _ _ family Z T conforming inside normal retain m full
  dsimp only
  intro radial γ gamma_positive margin in_domain first n fits
  dsimp only
  intro short δ room
  let K := T.roof conforming inside
  let P := T.pairedFolding.projectedBoundaryChain full
  let actual := full.interval first (n + 1) fits
  let window := T.pairedFolding.projectedBoundaryChain actual
  have geometry : window = P.interval first (n + 2) (by omega) :=
    T.pairedFolding.projectedBoundaryChain_interval full first (n + 1) fits
  have first_nonzero : P.edge 0 ≠ 0 := K.projectedBoundaryChain_edge_ne_zero full 0
  have genuine (i : Fin (n + 1)) : window.internalSourceRay (P.vertex 0) i ≠ 0 := by
    change window.vertex i.succ.castSucc - P.vertex 0 ≠ 0
    rw [geometry]
    exact P.sourceStart_vertex_ne_zero radial first_nonzero
      ⟨first + (i.val + 1), by have bound := i.isLt; omega⟩
      (by change 0 < first + (i.val + 1); omega)
  obtain ⟨q, near_source, strict, initial, angle_bound⟩ :=
    P.exists_near_sourceStart_strict_with_bound gamma_positive radial first_nonzero margin
      (fun q => ∑ k : Fin n, InnerProductGeometry.angle
        (window.internalSourceRay q k.castSucc) (window.internalSourceRay q k.succ))
      (window.continuousAt_internalSourceAngleSum (P.vertex 0) genuine) short (half_pos room)
  have comparisons := uniform family T conforming inside normal retain full q strict initial
    in_domain
  obtain ⟨cut, s, t, start, finish, q', c, height, nearby, trimmed_radial, trimmed_initial,
    supported, excluded, outward, jordan, E, preserved, estimate⟩ :=
    comparisons first n fits angle_bound (δ := δ / 2) (half_pos room)
  refine ⟨cut, s, t, start, finish, q', c, height, ?_, trimmed_radial, trimmed_initial,
    supported, excluded, outward, jordan, E, preserved, estimate⟩
  calc
    dist q' (P.vertex 0) ≤ dist q' q + dist q (P.vertex 0) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add nearby near_source
    _ = δ := by ring

end Unfoldings.SpatialEnvelope.Triangulation
