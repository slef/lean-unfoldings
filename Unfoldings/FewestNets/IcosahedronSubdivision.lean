module

public import Unfoldings.FewestNets.IcosahedronFaceIsometry
public import Unfoldings.Geometry.TriangleGridCover
public import Unfoldings.Geometry.ConvexRayBoundary
public import Unfoldings.Geometry.RadialTriangleHull

/-! The actual radially projected fine mesh covers every direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real NormedSpace
open scoped BigOperators
open TriangleGrid (Valid)

/-- A small grid cell within an original macroface. -/
abbrev GridCell (q : ℕ) :=
  {t : Fin (q + 1) × Fin (q + 1) × Bool // Valid q t.1.val t.2.1.val t.2.2}

/-- A labeled small chord triangle is a macroface together with a grid cell. -/
abbrev MeshFace (q : ℕ) := Fin 20 × GridCell q

def chordCorners {q : ℕ} (t : MeshFace q) : Fin 3 → Space :=
  let v := faceCorners t.1
  TriangleGrid.cellCorners (v 0) (v 1) (v 2) q t.2.val.1.val t.2.val.2.1.val t.2.val.2.2

def inscribedCorners {q : ℕ} (t : MeshFace q) (k : Fin 3) : Space :=
  normalize (chordCorners t k)

private theorem range_faceCorners (f : Fin 20) :
    (![faceCorners f 0, faceCorners f 1, faceCorners f 2] : Fin 3 → Space) = faceCorners f := by
  funext k
  fin_cases k <;> rfl

theorem chordTriangle_subset_faceTriangle {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    convexHull ℝ (Set.range (chordCorners t)) ⊆ faceTriangle t.1 := by
  rw [faceTriangle, ← range_faceCorners t.1]
  exact TriangleGrid.cell_subset_triangle _ _ _ hq t.2.property

theorem exists_chordTriangle_of_frontier {q : ℕ} (hq : 0 < q)
    {x : Space} (hx : x ∈ frontier hull) :
    ∃ t : MeshFace q, x ∈ convexHull ℝ (Set.range (chordCorners t)) := by
  obtain ⟨f, hx⟩ := Set.mem_iUnion.mp (frontier_hull_subset_faces hx)
  rw [faceTriangle, ← range_faceCorners f] at hx
  obtain ⟨i, j, upper, valid, cell⟩ :=
    TriangleGrid.exists_cell_of_mem_triangle _ _ _ hq hx
  have ile : i < q + 1 := by unfold Valid at valid; omega
  have jle : j < q + 1 := by unfold Valid at valid; omega
  exact ⟨⟨f, ⟨(⟨i, ile⟩, ⟨j, jle⟩, upper), valid⟩⟩, cell⟩

theorem chordCorners_ne_zero {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    chordCorners t k ≠ 0 := by
  intro zero
  have member := chordTriangle_subset_faceTriangle hq t
    (subset_convexHull ℝ _ (Set.mem_range_self k))
  rw [faceTriangle_eq_support] at member
  have eq : inner ℝ (faceNormal t.1) (chordCorners t k) = 2 + 3 * goldenRatio := member.2
  rw [zero, inner_zero_right] at eq
  linarith only [eq, goldenRatio_pos]

theorem inscribedCorners_unit {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    ‖inscribedCorners t k‖ = 1 :=
  norm_normalize (chordCorners_ne_zero hq t k)

/-- The cones of normalized grid triangles cover all of space. -/
theorem radialMesh_cover {q : ℕ} (hq : 0 < q) (x : Space) :
    ∃ t : MeshFace q, x ∈ radialTriangleCone (inscribedCorners t) := by
  by_cases zero : x = 0
  · let t : MeshFace q :=
      ⟨0, ⟨(⟨0, by omega⟩, ⟨0, by omega⟩, false), by simp [Valid]; omega⟩⟩
    exact ⟨t, ⟨fun _ => 0, fun _ => le_rfl, by simp [zero]⟩⟩
  obtain ⟨a, apos, ray⟩ := exists_frontier_on_positive_ray
    ((Set.finite_range rawVertex).isCompact_convexHull ℝ) (convex_convexHull ℝ _)
    zero_mem_interior_hull zero
  have boundary : a • x ∈ frontier hull := by simpa only [hull, zero_add, sub_zero] using ray
  obtain ⟨t, ht⟩ := exists_chordTriangle_of_frontier hq boundary
  obtain ⟨w, nonnegative, _, hx⟩ :=
    TriangleGrid.exists_weights_of_mem_convexHull_range _ ht
  refine ⟨t, ⟨fun k => (a⁻¹ * w k) * ‖chordCorners t k‖,
    fun k => mul_nonneg (mul_nonneg (inv_nonneg.mpr apos.le) (nonnegative k)) (norm_nonneg _),
    ?_⟩⟩
  simp_rw [mul_smul, inscribedCorners, norm_smul_normalize, ← Finset.smul_sum, hx]
  rw [smul_smul, inv_mul_cancel₀ apos.ne', one_smul]

end Unfoldings.FewestNets.Icosahedron
