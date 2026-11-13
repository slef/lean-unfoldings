module

public import Unfoldings.Roof.RestrictedBoundaryExistence
public import Unfoldings.Roof.SelectionComplement
public import Unfoldings.Geometry.TriangleUnionInterior

/-! Disk and simple-boundary conclusions for whole-edge connected roof patches without holes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- A whole-face roof patch with connected interior and complement has one Jordan boundary.
All banks and possible vertex contacts are the actual original geometric ones. -/
theorem restricted_frontier_isJordan_of_connected (U : Set Face)
    (inside : IsConnected (interior (K.restrictedCarrier U)))
    (outside : IsConnected (K.restrictedCarrier U)ᶜ) :
    Schoenflies.IsJordanCurve (frontier (K.restrictedCarrier U)) := by
  have nonempty : U.Nonempty := by
    obtain ⟨p, hp⟩ := inside.nonempty
    obtain ⟨f, _⟩ := Set.mem_iUnion.mp (interior_subset hp)
    exact ⟨f.val, f.property⟩
  obtain ⟨bank⟩ := K.exists_restricted_bank U nonempty
  obtain ⟨J, jordan, boundary⟩ := K.exists_Jordan_restricted_frontier U bank
  have regular := TriangleFamily.closure_interior_union
    (fun f : {f : Face // f ∈ U} => K.projectedTriangle f.val)
  rw [PlanarTopology.frontier_eq_of_Jordan_frontier_subset (K.compact_restrictedCarrier U)
    regular inside outside jordan boundary]
  exact jordan

open Classical in
/-- Connected interior and absence of holes construct an actual closed-disk homeomorphism. -/
theorem exists_restricted_disk_of_connected (U : Set Face)
    (inside : IsConnected (interior (K.restrictedCarrier U)))
    (outside : IsConnected (K.restrictedCarrier U)ᶜ) :
    Nonempty (K.restrictedCarrier U ≃ₜ Metric.closedBall (0 : Plane) 1) :=
  PlanarTopology.exists_diskHomeomorph_of_compact_Jordan_frontier
    (K.compact_restrictedCarrier U) inside.nonempty
    (K.restricted_frontier_isJordan_of_connected U inside outside)

open Classical in
/-- Whole-edge connected roof faces have connected geometric interior. -/
theorem isConnected_interior_restrictedCarrier (U : Set Face) (nonempty : U.Nonempty)
    (connected : ∀ f g : {f : Face // f ∈ U}, Relation.ReflTransGen
      (TriangleFamily.EdgeAdjacent
        (fun f : {f : Face // f ∈ U} => K.projectedTriangle f.val)) f g) :
    IsConnected (interior (K.restrictedCarrier U)) := by
  have : Nonempty {f : Face // f ∈ U} := nonempty.to_subtype
  apply TriangleFamily.isConnected_interior_union _ _ connected
  intro f g different
  exact K.projectedTriangles_nonoverlapping (fun same => different (Subtype.ext same))

open Classical in
/-- A nonempty whole-edge connected convex-gradient selection has simple Jordan boundary. -/
theorem selected_frontier_isJordan {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes)
    (nonempty : {f : Face | K.normalSlope f ∈ slopes}.Nonempty)
    (connected : ∀ f g : {f : Face // K.normalSlope f ∈ slopes}, Relation.ReflTransGen
      (TriangleFamily.EdgeAdjacent
        (fun f : {f : Face // K.normalSlope f ∈ slopes} => K.projectedTriangle f.val)) f g) :
    Schoenflies.IsJordanCurve (frontier (K.selectedCarrier slopes)) := by
  apply K.restricted_frontier_isJordan_of_connected {f | K.normalSlope f ∈ slopes}
  · exact K.isConnected_interior_restrictedCarrier _ nonempty connected
  · exact K.isConnected_compl_selectedCarrier convex closed
      ⟨K.normalSlope nonempty.choose, nonempty.choose_spec⟩

open Classical in
/-- The actual geometric union of a whole-edge connected convex-gradient selection is a disk.
The hypotheses describe only the input gradients and finite face connectivity. -/
theorem exists_selected_disk {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes)
    (nonempty : {f : Face | K.normalSlope f ∈ slopes}.Nonempty)
    (connected : ∀ f g : {f : Face // K.normalSlope f ∈ slopes}, Relation.ReflTransGen
      (TriangleFamily.EdgeAdjacent
        (fun f : {f : Face // K.normalSlope f ∈ slopes} => K.projectedTriangle f.val)) f g) :
    Nonempty (K.selectedCarrier slopes ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  apply K.exists_restricted_disk_of_connected {f | K.normalSlope f ∈ slopes}
  · exact K.isConnected_interior_restrictedCarrier _ nonempty connected
  · exact K.isConnected_compl_selectedCarrier convex closed
      ⟨K.normalSlope nonempty.choose, nonempty.choose_spec⟩

end Unfoldings.ConvexRoof
