module

public import Unfoldings.FewestNets.IcosahedronMeshHinges
public import Unfoldings.Geometry.RadialLinearCoverConvex
public import Unfoldings.Geometry.RadialHullSupport

/-! The fine radial triangles are supporting triangles of the inscribed convex hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Set
open scoped BigOperators

def hullGauge {q : ℕ} (hq : 0 < q) (x : Space) : ℝ :=
  meshGauge hq (radialMesh_cover hq x).choose x

theorem hullGauge_eq_meshGauge {q : ℕ} (hq : 0 < q) (t : MeshFace q) {x : Space}
    (hx : x ∈ radialTriangleCone (inscribedCorners t)) :
    hullGauge hq x = meshGauge hq t x :=
  meshGauge_eq_of_mem_cones hq _ t (radialMesh_cover hq x).choose_spec hx

theorem hullGauge_zero {q : ℕ} (hq : 0 < q) : hullGauge hq 0 = 0 :=
  map_zero _

theorem continuous_hullGauge {q : ℕ} (hq : 0 < q) : Continuous (hullGauge hq) := by
  let cell (t : MeshFace q) := radialTriangleCone (inscribedCorners t)
  exact (locallyFinite_of_finite cell).continuous (iUnion_eq_univ_iff.mpr (radialMesh_cover hq))
    (fun t => isClosed_radialTriangleCone (linearIndependent_inscribedCorners hq t))
    (fun t => (meshGauge hq t).continuous_of_finiteDimensional.continuousOn.congr
      (fun _ => hullGauge_eq_meshGauge hq t))

theorem convexOn_hullGauge {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    ConvexOn ℝ Set.univ (hullGauge hq) := by
  apply convexOn_univ_of_radial_linear_cover
    (fun t : MeshFace q => radialTriangleCone (inscribedCorners t))
    (fun t => isClosed_radialTriangleCone (linearIndependent_inscribedCorners hq t))
    (fun t => convex_radialTriangleCone (linearIndependent_inscribedCorners hq t))
    (radialMesh_cover hq) (hullGauge hq) (meshGauge hq)
    (fun t _ => hullGauge_eq_meshGauge hq t)
    (fun label : MeshFace q × Fin 3 => inscribedCorners label.1 label.2)
  intro x off t s ht hs z hz
  exact meshGauge_le_on_neighbor qbig hq t s (fun k r => off (t, k) r) ht hs hz

def meshSites (q : ℕ) : Set Space :=
  Set.range (fun label : MeshFace q × Fin 3 => inscribedCorners label.1 label.2)

def meshHull (q : ℕ) : Set Space := convexHull ℝ (insert 0 (meshSites q))

theorem meshHull_eq_sublevel {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    meshHull q = {x | hullGauge hq x ≤ 1} :=
  convexHull_eq_sublevel_of_radial_triangles inscribedCorners (radialMesh_cover hq)
    (hullGauge hq) (convexOn_hullGauge qbig hq) (meshGauge hq)
    (meshGauge_corner hq) (fun t _ => hullGauge_eq_meshGauge hq t)

theorem zero_mem_interior_meshHull {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    (0 : Space) ∈ interior (meshHull q) := by
  rw [meshHull_eq_sublevel qbig hq]
  let U : Set Space := {x | hullGauge hq x < 1}
  have sub : U ⊆ {x | hullGauge hq x ≤ 1} := fun _ (hx : hullGauge hq _ < 1) => hx.le
  have open_U : IsOpen U := isOpen_lt (continuous_hullGauge hq) continuous_const
  have zero : (0 : Space) ∈ U := by
    change hullGauge hq 0 < 1
    rw [hullGauge_zero]
    norm_num
  exact interior_maximal sub open_U zero

/-- Every fine mesh plane supports the convex body formed by the unit sites. -/
theorem meshGauge_le_one_of_mem_hull {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) {x : Space} (hx : x ∈ meshHull q) : meshGauge hq t x ≤ 1 :=
  radialTriangle_supports_hull inscribedCorners (radialMesh_cover hq) (hullGauge hq)
    (convexOn_hullGauge qbig hq) (meshGauge hq) (meshGauge_corner hq)
    (fun s _ => hullGauge_eq_meshGauge hq s) t (linearIndependent_inscribedCorners hq t) x hx

end Unfoldings.FewestNets.Icosahedron
