module

public import Unfoldings.Cap.GeometricSectorTails

/-! Constructed actual cut tails merge permanently and retain a consistent sweep order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

def geometricTailStartHeight (i : FiveSector) (w : F.GeometricVertex) : ℝ :=
  let P := M.geometricRootPath F covered positive small lower
    (fiveSectorFrame t positive small i).place w
  (P.vertex 0).re + (P.vertex 0).im

def geometricTailEndHeight (i : FiveSector) (w : F.GeometricVertex) : ℝ :=
  let P := M.geometricRootPath F covered positive small lower
    (fiveSectorFrame t positive small i).place w
  (P.vertex (Fin.last _)).re + (P.vertex (Fin.last _)).im

/-- An exact height-graph representation of one actual geometric parent path. -/
structure SectorTailGraph (i : FiveSector) (w : F.GeometricVertex) where
  graph : MonotoneHeightGraph
  vertices :
    let P := M.geometricRootPath F covered positive small lower
      (fiveSectorFrame t positive small i).place w
    ∀ j, graph.coordinate ((P.vertex j).re + (P.vertex j).im) = (P.vertex j).re
  pieces :
    let P := M.geometricRootPath F covered positive small lower
      (fiveSectorFrame t positive small i).place w
    ∀ j (s : unitInterval),
      graph.coordinate ((P.point j s).re + (P.point j s).im) = (P.point j s).re
  positive_steps :
    let P := M.geometricRootPath F covered positive small lower
      (fiveSectorFrame t positive small i).place w
    ∀ j, 0 < (P.edge j).re ∧ 0 < (P.edge j).im
  covered : ∀ h : ℝ, M.geometricTailStartHeight F covered positive small lower i w ≤ h →
    h < M.geometricTailEndHeight F covered positive small lower i w →
      graph.point h ∈ (M.sectorHeightNetwork F covered positive small lower i).carrier

/-- Construct the representation from the component's actual sector directions. -/
def sectorTailGraph (c : F.Component) (i : FiveSector)
    (directions : ∀ z : F.GeometricVertex,
      z ∉ (M.geometricParents F covered positive small lower).roots →
      M.geometricComponent F covered z = c →
        F.geometricPosition (M.geometricParent F covered z) - F.geometricPosition z ∈
          closedFiveSector t i)
    (w : F.GeometricVertex) (component : M.geometricComponent F covered w = c) :
    M.SectorTailGraph F covered positive small lower i w :=
  Classical.choice (by
    obtain ⟨G, vertices, pieces, coverage⟩ :=
      M.exists_sector_tail_heightGraph F covered positive small lower c i directions w component
    exact ⟨⟨G, vertices, pieces,
      M.geometricRootPath_coordinates_of_component_sector F covered positive small lower
        c i directions w component, coverage⟩⟩)

namespace SectorTailGraph

variable {M F covered positive small lower} {i : FiveSector} {w z : F.GeometricVertex}

/-- Two actual tails in the same sector cannot split after meeting, up to their outer tips. -/
theorem coalesces (A : M.SectorTailGraph F covered positive small lower i w)
    (B : M.SectorTailGraph F covered positive small lower i z) {a b : ℝ}
    (first_start : M.geometricTailStartHeight F covered positive small lower i w ≤ a)
    (last_start : M.geometricTailStartHeight F covered positive small lower i z ≤ a)
    (first_end : b < M.geometricTailEndHeight F covered positive small lower i w)
    (last_end : b < M.geometricTailEndHeight F covered positive small lower i z) :
    A.graph.CoalescesOn B.graph a b :=
  (M.sectorHeightNetwork F covered positive small lower i).graphs_coalesce A.graph B.graph
    (fun h member => A.covered h (first_start.trans member.1) (member.2.trans_lt first_end))
    (fun h member => B.covered h (last_start.trans member.1) (member.2.trans_lt last_end))

/-- Different branches and different components share one weak order on a common sweep slab. -/
theorem order_total (A : M.SectorTailGraph F covered positive small lower i w)
    (B : M.SectorTailGraph F covered positive small lower i z) {a b : ℝ}
    (first_start : M.geometricTailStartHeight F covered positive small lower i w ≤ a)
    (last_start : M.geometricTailStartHeight F covered positive small lower i z ≤ a)
    (first_end : b < M.geometricTailEndHeight F covered positive small lower i w)
    (last_end : b < M.geometricTailEndHeight F covered positive small lower i z) :
    (∀ h ∈ Set.Icc a b, A.graph.coordinate h ≤ B.graph.coordinate h) ∨
      (∀ h ∈ Set.Icc a b, B.graph.coordinate h ≤ A.graph.coordinate h) :=
  (A.coalesces B first_start last_start first_end last_end).order_total A.graph B.graph a b

end SectorTailGraph
end Unfoldings.ConvexCap.SectorForest
