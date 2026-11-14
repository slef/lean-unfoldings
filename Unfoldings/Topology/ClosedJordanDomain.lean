module

public import Unfoldings.Topology.AmbientJordanDisk
public import Unfoldings.Topology.EscapeRays
public import Schoenflies.JordanClosed

/-! The actual bounded Jordan filling is a compact regular disk with its exact original frontier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

def closedJordanDomain (J : Set Plane) : Set Plane := closure (Schoenflies.inside J)

theorem isCompact_closedJordanDomain {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) :
    IsCompact (closedJordanDomain J) :=
  (Schoenflies.jordan_curve_theorem jordan).isBounded_inside.isCompact_closure

theorem regular_closedJordanDomain {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) :
    closure (interior (closedJordanDomain J)) = closedJordanDomain J := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_mono
    exact (Schoenflies.jordan_curve_theorem jordan).isOpen_inside.subset_interior_iff.mpr
      subset_closure

theorem interior_closedJordanDomain_nonempty {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) : (interior (closedJordanDomain J)).Nonempty := by
  have inside := (Schoenflies.jordan_curve_theorem jordan).isConnected_inside.nonempty
  exact inside.mono ((Schoenflies.jordan_curve_theorem jordan).isOpen_inside.subset_interior_iff.mpr
    subset_closure)

theorem frontier_closedJordanDomain {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) :
    frontier (closedJordanDomain J) = J := by
  let separation := Schoenflies.jordan_curve_theorem jordan
  have closure_avoids : closedJordanDomain J ⊆ (Schoenflies.outside J)ᶜ :=
    closure_minimal
      (fun x hx => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hx)
      separation.isOpen_outside.isClosed_compl
  have outside_avoids : Schoenflies.outside J ⊆ (interior (closedJordanDomain J))ᶜ := by
    intro x hx inside
    exact closure_avoids (interior_subset inside) hx
  have closed_outside_avoids := closure_minimal outside_avoids isOpen_interior.isClosed_compl
  apply Set.Subset.antisymm
  · exact frontier_closure_subset.trans separation.frontier_inside.subset
  · intro x hx
    have closure_inside : x ∈ closedJordanDomain J :=
      frontier_subset_closure (separation.frontier_inside.symm ▸ hx)
    have closure_outside : x ∈ closure (Schoenflies.outside J) :=
      frontier_subset_closure (separation.frontier_outside.symm ▸ hx)
    rw [frontier]
    exact ⟨subset_closure closure_inside, closed_outside_avoids closure_outside⟩

theorem exists_ambient_closedJordanDomain_disk {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) :
    ∃ F : Plane ≃ₜ Plane, F '' closedJordanDomain J = Metric.closedBall (0 : Plane) 1 := by
  apply exists_ambientDiskHomeomorph (isCompact_closedJordanDomain jordan)
    (interior_closedJordanDomain_nonempty jordan)
  rwa [frontier_closedJordanDomain jordan]

/-- Any compact convex container of the actual curve also contains its whole bounded filling. -/
theorem closedJordanDomain_subset_convex {J K : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (compact : IsCompact K) (convex : Convex ℝ K)
    (contains : J ⊆ K) : closedJordanDomain J ⊆ K := by
  have nonempty : K.Nonempty := jordan.nonempty.mono contains
  have connected := isConnected_compl_of_escape_rays compact (fun p hp =>
    exists_escape_ray_of_not_mem_closed_convex convex compact.isClosed nonempty hp)
  exact closure_minimal (inside_subset_of_isConnected_compl compact connected contains)
    compact.isClosed

/-- If the curve is strictly inside its container, its whole filling is strictly inside too. -/
theorem closedJordanDomain_subset_interior {J K : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (contained : closedJordanDomain J ⊆ K)
    (boundary : J ⊆ interior K) : closedJordanDomain J ⊆ interior K := by
  let separation := Schoenflies.jordan_curve_theorem jordan
  have open_inside : Schoenflies.inside J ⊆ interior K :=
    separation.isOpen_inside.subset_interior_iff.mpr (subset_closure.trans contained)
  intro x hx
  by_cases on_curve : x ∈ J
  · exact boundary on_curve
  · apply open_inside
    by_contra outside
    have frontier : x ∈ frontier (Schoenflies.inside J) := by
      rw [frontier, separation.isOpen_inside.interior_eq]
      exact ⟨hx, outside⟩
    exact on_curve (separation.frontier_inside.subset frontier)

end Unfoldings.PlanarTopology
