module

public import Unfoldings.Source.Coordinates

/-!
# The closed source cut locus

Take the closure of points with two distinct normalized shortest paths. This
retains possible cone leaves with a unique incoming path. The definition alone
does not assert a finite graph or the required polyhedral leaf characterization.
A genuine source chart excludes a whole ball from this closed set.
-/

@[expose] public section

open scoped ENNReal

namespace Unfoldings

variable {X : Type*} [MetricSpace X]

def nonuniqueSourcePoints (source : X) : Set X :=
  {x | ∃ p q : Path source x, p.IsGeodesic ∧ q.IsGeodesic ∧ p ≠ q}

def sourceCutLocus (source : X) : Set X := closure (nonuniqueSourcePoints source)

theorem isClosed_sourceCutLocus (source : X) : IsClosed (sourceCutLocus source) :=
  isClosed_closure

theorem nonuniqueSourcePoints_subset_cutLocus (source : X) :
    nonuniqueSourcePoints source ⊆ sourceCutLocus source := subset_closure

theorem geodesic_unique_off_cutLocus {source target : X} (outside : target ∉ sourceCutLocus source)
    {p q : Path source target} (geodesic : p.IsGeodesic) (other : q.IsGeodesic) : p = q := by
  by_contra different
  exact outside (subset_closure ⟨p, q, geodesic, other, different⟩)

namespace SourceFrame

variable {source : X} (R : SourceFrame source)

theorem cutLocus_subset_outside_source_ball :
    sourceCutLocus source ⊆ (Metric.eball source (ENNReal.ofReal R.radius))ᶜ := by
  apply closure_minimal _ Metric.isOpen_eball.isClosed_compl
  intro target nonunique inside
  obtain ⟨p, q, geodesic, other, different⟩ := nonunique
  apply different
  exact geodesic.eq_of_eball_chart other source (ENNReal.ofReal R.radius) R.chart
    (by simpa only [edist_self, zero_add, Metric.mem_eball, edist_comm] using inside)

include R in
theorem source_not_mem_cutLocus : source ∉ sourceCutLocus source := by
  intro member
  exact R.cutLocus_subset_outside_source_ball member R.sourcePoint.property

end SourceFrame
end Unfoldings
