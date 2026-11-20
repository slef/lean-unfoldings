module

public import Unfoldings.Metric.FlatPlanarGluing
public import Unfoldings.Metric.RigidFrameDescent
public import Mathlib.Topology.Connected.Clopen

/-! Global development of a locally Euclidean boundary gluing from a proper collapse. -/

@[expose] public section

noncomputable section

open Set Topology

namespace Unfoldings.MetricGluing

variable {I : Type*} [Finite I] (cells : I → Set Plane)
  (glue : Total (fun i => cells i) → Total (fun i => cells i) → Prop)

local notation "X" => Realization (fun i => cells i) glue

/-- A proper surjection to a contractible target with contractible fibers
supplies the global isometry of a locally Euclidean finite boundary gluing. -/
theorem exists_global_planar_isometry_of_proper_contractible_fibers
    {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]
    (collapse : X → Y) (proper : IsProperMap collapse) (onto : Function.Surjective collapse)
    (fibers : ∀ y, ContractibleSpace (collapse ⁻¹' {y}))
    (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty)
    (boundary : ∀ i x, x ∈ seamSupport (fun i => cells i) glue i →
      x.val ∉ interior (cells i))
    (regular : ∀ x : X, HasMetricBallChart Plane x) :
    ∃ f : X → Plane, Isometry f ∧ Function.Surjective f := by
  have quotient := proper.isClosedMap.isQuotientMap proper.continuous onto
  have connected_fibers (y : Y) : IsConnected (collapse ⁻¹' {y}) := by
    let : ContractibleSpace (collapse ⁻¹' {y}) := fibers y
    exact isConnected_iff_connectedSpace.mpr inferInstance
  have connected : IsConnected (univ : Set X) := by
    have h := quotient.isCoinducing.isConnected_preimage_of_isClosed connected_fibers
      isClosed_univ (isConnected_univ (α := Y))
    rwa [preimage_univ] at h
  let : PreconnectedSpace X := ⟨connected.2⟩
  let : Nonempty X := ⟨connected.1.choose⟩
  let : MetricSpace X := EMetricSpace.toMetricSpace edist_ne_top_of_preconnected
  let A := EuclideanAtlas.ofRegular regular
  obtain ⟨f, local_isometry⟩ := A.exists_local_isometry_of_proper_contractible_fibers collapse
    proper onto fibers
  exact exists_global_planar_isometry_of_local_isometry cells glue closed convex full boundary
    regular f local_isometry

end Unfoldings.MetricGluing
