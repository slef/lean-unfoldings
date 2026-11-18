module

public import Unfoldings.Roof.SupportedBankWindows
public import Unfoldings.Roof.SpatialEnvelopeInteriorBanks
public import Unfoldings.Polyhedron.ProjectedBoundaryChainInterval

/-! Uniform physical comparisons for all short windows of an actual radial mesh bank chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

local instance bankWindowMeshIndexFintype {I : Type u} [Fintype I] [Nonempty I]
    {family : I → SpatialPlane} {Z : ℝ} (T : Triangulation family Z) : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite


open Classical in
/-- One tilt works for every mesh and every admissible short actual radial bank window. -/
theorem exists_uniform_spatial_mesh_bank_windows {η : ℝ} (error_positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {I : Type u} [Fintype I] [Nonempty I] (family : I → SpatialPlane) {Z : ℝ}
        (T : Triangulation family Z) (conforming : TriangleFamily.Conforming T.projectedTriangle)
        (inside : (interior (clip family Z)).Nonempty),
        (∀ i, Real.cos φ ≤ (family i).normal 2) →
        ∀ (retain : Set T.pairedComplex.Seam) {m : ℕ}
          (full : (T.pairedComplex.boundarySystem retain).Chain m) (control : Plane),
          control ∈ (T.pairedFolding.projectedBoundaryChain full).strictRadialSources →
          0 < dist control ((T.pairedFolding.projectedBoundaryChain full).vertex 0) →
          (∀ j, Cap.horizontal (T.pairedFolding.boundaryPosition (full.point j)) ∈
            interior (clip family Z)) →
          (T.roof conforming inside).SupportedBankWindowComparisons φ η retain full control := by
  obtain ⟨φ, bounds, uniform⟩ := ConvexRoof.exists_uniform_supported_original_bank_window.{0, 0}
    error_positive
  refine ⟨φ, bounds, ?_⟩
  intro I _ _ family Z T conforming inside normal retain m full control strict initial in_domain
    first n fits
  dsimp only
  intro short δ room
  let actual := full.interval first (n + 1) fits
  let P := T.pairedFolding.projectedBoundaryChain actual
  let base := T.pairedFolding.projectedBoundaryChain full
  have cut (j : Fin (n + 2)) : ¬ T.pairedComplex.IsBoundaryEdge Set.univ
      (T.pairedComplex.germEdge (actual.point j).val) :=
    T.boundaryEnd_is_cut_of_projected_mem_interior conforming inside retain _
      (in_domain (full.intervalIndex first (n + 1) fits j))
  have geometry : P = base.interval first (n + 2) (by omega) :=
    T.pairedFolding.projectedBoundaryChain_interval full first (n + 1) fits
  have strict_interval : control ∈ (base.interval first (n + 2) (by
    omega)).strictRadialSources := by
    intro j nonzero
    exact strict ⟨first + j.val, by have bound := j.isLt; omega⟩ nonzero
  have strict_P : control ∈ P.strictRadialSources := Eq.mpr
    (congrArg (fun A : PolygonalChain Plane (n + 2) => control ∈ A.strictRadialSources) geometry)
    strict_interval
  have radial := base.radialFrom_of_strictRadialSource strict
  have lower := radial.dist_vertices_le base 0 ⟨first, by omega⟩ le_rfl (Fin.zero_le _)
  have initial_interval : 0 < dist control ((base.interval first (n + 2) (by omega)).vertex 0) :=
    initial.trans_le lower
  have initial_P : 0 < dist control (P.vertex 0) := Eq.mpr
    (congrArg (fun A : PolygonalChain Plane (n + 2) => 0 < dist control (A.vertex 0)) geometry)
    initial_interval
  have tilt : (T.roof conforming inside).TiltBound φ := fun f => normal (T.support f)
  obtain ⟨s, t, start, finish, q, c, height, nearby, trimmed_radial, trimmed_initial,
      supported, excluded, outward, jordan, E, preserved, estimate⟩ :=
    uniform (T.roof conforming inside) tilt retain actual cut control strict_P initial_P short room
  exact ⟨cut, s, t, start, finish, q, c, height, nearby, trimmed_radial, trimmed_initial,
    supported, excluded, outward, jordan, E, preserved, estimate⟩

end Unfoldings.SpatialEnvelope.Triangulation
