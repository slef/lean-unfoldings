module

public import Unfoldings.Cap.GnomonicArea

public import Unfoldings.Roof.Gnomonic
public import Unfoldings.Roof.NormalAreaThreshold
public import Unfoldings.Geometry.Normalize
public import Unfoldings.Geometry.EuclideanArea

/-!
# The actual spherical normal image has no more area than its slope polygon

The inverse gnomonic map is nonexpansive for ambient chord distance. Normalized
Euclidean Hausdorff measure therefore bounds its spherical area by planar
Lebesgue area, with no differentiability or nondegeneracy assumptions.
Identification of intrinsic angular defect with this area remains separate.
-/

@[expose] public section

noncomputable section



namespace Unfoldings.ConvexRoof

open MeasureTheory

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The actual unit spherical normal image of an original vertex. -/
def sphericalNormalPolygon (v : C.Vertex Set.univ) : Set Space :=
  Cap.gnomonicNormal '' K.normalPolygon v

theorem sphericalNormalPolygon_unit {v : C.Vertex Set.univ} {n : Space}
    (present : n ∈ K.sphericalNormalPolygon v) : ‖n‖ = 1 ∧ 0 < n 2 := by
  obtain ⟨g, _, rfl⟩ := present
  exact ⟨Cap.gnomonicNormal_unit g, Cap.gnomonicNormal_upward g⟩

theorem compact_sphericalNormalPolygon (v : C.Vertex Set.univ) :
    IsCompact (K.sphericalNormalPolygon v) :=
  (K.compact_normalPolygon v).image Cap.gnomonicNormal_lipschitz.continuous

/-- Every incident face normal occurs in its actual vertex normal image. -/
theorem normal_mem_sphericalNormalPolygon (f : Face) (i : Fin 3) :
    K.normal f ∈ K.sphericalNormalPolygon (C.vertexOfCorner Set.univ (f, i)) := by
  refine ⟨K.normalSlope f, subset_convexHull ℝ _ ⟨f, i, rfl, rfl⟩, ?_⟩
  exact K.gnomonicNormal_normalSlope f

/-- Every point of the spherical polygon supports the entire actual cap at the vertex. -/
theorem sphericalNormalPolygon_supports {v : C.Vertex Set.univ} {n : Space}
    (present : n ∈ K.sphericalNormalPolygon v) (h : Face) (x : C.Cell h) :
    inner ℝ n (K.folding.place h x.val -
      K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)) ≤ 0 := by
  obtain ⟨g, inside, rfl⟩ := present
  obtain ⟨⟨f, i⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
  have support := K.normalPolygon_supports _ inside (K.projectFace h x.val)
  rw [K.projectedVertex_ofCorner] at support
  have vertex_height := K.roofHeight_face f
    ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i⟩
  have point_height := K.roofHeight_face h x
  change K.roofHeight (K.projectFace h x.val) ≤
    K.roofHeight (K.projectFace f ((C.triangle f).vertex i)) -
      inner ℝ g (K.projectFace h x.val - K.projectFace f ((C.triangle f).vertex i)) at support
  rw [point_height, vertex_height] at support
  rw [C.vertexPoint_vertexOfCorner, Cap.gnomonicNormal, NormedSpace.normalize]
  change inner ℝ (‖Cap.northLift g‖⁻¹ • Cap.northLift g)
    (K.folding.place h x.val - K.folding.place f ((C.triangle f).vertex i)) ≤ 0
  rw [real_inner_smul_left]
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
  rw [Cap.horizontal_inner, Cap.northLift_horizontal, Cap.northLift_height, map_sub]
  change inner ℝ g (K.projectFace h x.val - K.projectFace f ((C.triangle f).vertex i)) +
    1 * (K.folding.place h x.val 2 - K.folding.place f ((C.triangle f).vertex i) 2) ≤ 0
  linarith

theorem sphericalNormalPolygon_area_le (v : C.Vertex Set.univ) :
    μHE[2] (K.sphericalNormalPolygon v) ≤ volume (K.normalPolygon v) :=
  Cap.gnomonicNormal_area_le (K.normalPolygon v)

/-- The full spherical area budget remains independent of the number of vertices. -/
theorem sphericalNormalPolygon_area_budget {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) :
    (∑ v : C.Vertex Set.univ, μHE[2] (K.sphericalNormalPolygon v)) ≤
      ENNReal.ofReal (Real.sqrt (1 - c ^ 2) / c) ^ 2 * ENNReal.ofReal Real.pi := by
  exact (Finset.sum_le_sum (fun v _ => K.sphericalNormalPolygon_area_le v)).trans
    (K.normalPolygon_area_budget positive height)

/-- A positive uniform tilt threshold makes the complete spherical normal area small. -/
theorem exists_tilt_spherical_normal_area_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ K : ConvexRoof C, K.TiltBound φ →
      (∑ v : C.Vertex Set.univ, μHE[2] (K.sphericalNormalPolygon v)) < ENNReal.ofReal ε := by
  obtain ⟨φ, bounds, area⟩ := exists_tilt_normal_area_lt (C := C) positive
  refine ⟨φ, bounds, fun K tilt => ?_⟩
  exact (Finset.sum_le_sum (fun v _ => K.sphericalNormalPolygon_area_le v)).trans_lt
    (area K tilt)

end Unfoldings.ConvexRoof
