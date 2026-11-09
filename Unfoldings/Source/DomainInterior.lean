module

public import Unfoldings.Source.Domain
public import Unfoldings.Source.EndpointChart
public import Unfoldings.Source.EndpointStability
public import Unfoldings.Geometry.AffineEnd

/-!
# Regular unique endpoints give interior source vectors

The proved terminal affine formula holds for every shortest path to all
nearby endpoints, by compact singleton-fiber stability. Actual existence of
shortest paths covers the corresponding open rigid chart image. This proves
the source vector is interior to the constructed planar domain.
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X} (R : SourceFrame source)
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

include exists_paths

theorem coordinate_mem_interior_domain (p : SourcePath source)
    (regular : ∀ t, HasMetricBallChart Plane (p.path t))
    (unique : ∀ q : SourcePath source, q.target = p.target → q = p) :
    R.coordinate p.path p.geodesic ∈ interior R.domain := by
  obtain ⟨D, U, open_D, open_U, chart, A, W, nearby, inside, formula⟩ :=
    R.exists_endpoint_chart p regular
  obtain ⟨V, neighborhood, force⟩ := p.endpoint_neighborhood_of_unique unique nearby
  have in_W : p ∈ W := mem_of_mem_nhds nearby
  have in_D : p.target ∈ D := inside p in_W
  have both : V ∩ D ∈ 𝓝 p.target := Filter.inter_mem neighborhood (open_D.mem_nhds in_D)
  obtain ⟨Z, subset, open_Z, at_p⟩ := mem_nhds_iff.mp both
  let translation : Plane ≃ᵃⁱ[ℝ] Plane := AffineIsometryEquiv.vaddConst ℝ (-R.origin)
  let g : D → Plane := fun x => translation (A (chart x).val)
  have open_g : IsOpenMap g := translation.toHomeomorph.isOpenMap.comp
    ((affineIsometryEnd_isOpenMap A).comp
      (open_U.isOpenMap_subtype_val.comp chart.toHomeomorph.isOpenMap))
  let S : Set D := Subtype.val ⁻¹' Z
  have open_S : IsOpen S := open_Z.preimage continuous_subtype_val
  have included : g '' S ⊆ R.domain := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, target⟩ := exists_paths x.val
    have forced : q ∈ W := force q (by rw [target]; exact (subset hx).1)
    have actual := formula q forced
    have point : (⟨q.target, inside q forced⟩ : D) = x := Subtype.ext target
    rw [point] at actual
    have coordinate : R.coordinate q.path q.geodesic = g x := by
      change R.coordinate q.path q.geodesic = A (chart x).val + -R.origin
      simpa only [sub_eq_add_neg] using actual
    exact ⟨q, coordinate⟩
  have at_image : R.coordinate p.path p.geodesic ∈ g '' S := by
    refine ⟨⟨p.target, in_D⟩, at_p, ?_⟩
    change A (chart ⟨p.target, in_D⟩).val + -R.origin = R.coordinate p.path p.geodesic
    simpa only [sub_eq_add_neg] using (formula p in_W).symm
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset ((open_g S open_S).mem_nhds at_image) included)

end Unfoldings.SourceFrame
