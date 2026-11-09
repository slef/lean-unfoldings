module

public import Unfoldings.Polyhedron.GermDirections
public import Unfoldings.Polyhedron.GermEdges
public import Unfoldings.Complex.GermSegments

/-!
# Exact spatial radial directions of actual link germs

Points at any sufficiently small positive radius lift to regular points of
their original local edges. Equal unit directions give equal spatial lifts;
embeddedness and the exact seam classes then identify the germs precisely
up to their actual mate pairing.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

def germUnitDirection (p : C.Germ) : Space :=
  (‖F.germDirection p‖)⁻¹ • F.germDirection p

theorem norm_germUnitDirection (p : C.Germ) : ‖F.germUnitDirection p‖ = 1 := by
  rw [germUnitDirection, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (F.germDirection_ne_zero p))]

theorem germUnitDirection_mate (retain : Set C.Seam) (p : C.Germ) :
    F.germUnitDirection (C.mateGerm retain p) = F.germUnitDirection p := by
  unfold germUnitDirection
  rw [F.germDirection_mate]

def germRadiusCoordinate (p : C.Germ) (r : ℝ) : Plane :=
  AffineMap.lineMap
    ((C.triangle p.1.1).endpoint (C.germEdge p).edge p.2).val
    ((C.triangle p.1.1).endpoint (C.germEdge p).edge (!p.2)).val
    (r / ‖F.germDirection p‖)

theorem germRadius_parameter (p : C.Germ) {r : ℝ} (positive : 0 < r)
    (small : r < ‖F.germDirection p‖) :
    r / ‖F.germDirection p‖ ∈ Set.Ioo (0 : ℝ) 1 := by
  have length_positive := norm_pos_iff.mpr (F.germDirection_ne_zero p)
  exact ⟨div_pos positive length_positive, (div_lt_one length_positive).mpr small⟩

theorem germRadiusCoordinate_mem_edge (p : C.Germ) {r : ℝ} (positive : 0 < r)
    (small : r < ‖F.germDirection p‖) :
    F.germRadiusCoordinate p r ∈ (C.triangle p.1.1).edge (C.germEdge p).edge := by
  have parameter := F.germRadius_parameter p positive small
  exact (C.triangle p.1.1).lineMap_endpoints_mem_edge (C.germEdge p).edge p.2
    ⟨parameter.1.le, parameter.2.le⟩

theorem germRadiusCoordinate_not_vertex (p : C.Germ) {r : ℝ} (positive : 0 < r)
    (small : r < ‖F.germDirection p‖) :
    ¬ (C.triangle p.1.1).IsVertex (F.germRadiusCoordinate p r) :=
  (C.triangle p.1.1).lineMap_endpoints_not_vertex (C.germEdge p).edge p.2
    (F.germRadius_parameter p positive small)

theorem germRadiusCoordinate_spatial (p : C.Germ) (r : ℝ) :
    F.place p.1.1 (F.germRadiusCoordinate p r) =
      (r / ‖F.germDirection p‖) • F.germDirection p +
        F.place p.1.1 ((C.triangle p.1.1).vertex p.1.2) := by
  unfold germRadiusCoordinate
  rw [F.place_lineMap, C.germ_apex_endpoint, C.germ_far_endpoint,
    AffineMap.lineMap_apply_module']
  rfl

theorem germRadiusCoordinate_spatial_unit (p : C.Germ) (r : ℝ) :
    F.place p.1.1 (F.germRadiusCoordinate p r) = r • F.germUnitDirection p +
      F.place p.1.1 ((C.triangle p.1.1).vertex p.1.2) := by
  rw [F.germRadiusCoordinate_spatial, germUnitDirection, smul_smul, div_eq_mul_inv]

theorem linkGerm_unitDirection_eq_iff (embedded : F.IsEmbedded)
    {v : C.Vertex Set.univ} (p q : C.LinkGerm Set.univ v) :
    F.germUnitDirection p.val = F.germUnitDirection q.val ↔
      p = q ∨ C.linkMate Set.univ v p = q := by
  constructor
  · intro same_direction
    let r := min ‖F.germDirection p.val‖ ‖F.germDirection q.val‖ / 2
    have lp : 0 < ‖F.germDirection p.val‖ := norm_pos_iff.mpr (F.germDirection_ne_zero _)
    have lq : 0 < ‖F.germDirection q.val‖ := norm_pos_iff.mpr (F.germDirection_ne_zero _)
    have positive : 0 < r := div_pos (lt_min lp lq) (by norm_num)
    have small_p : r < ‖F.germDirection p.val‖ := by
      have bound := min_le_left ‖F.germDirection p.val‖ ‖F.germDirection q.val‖
      dsimp [r]
      linarith
    have small_q : r < ‖F.germDirection q.val‖ := by
      have bound := min_le_right ‖F.germDirection p.val‖ ‖F.germDirection q.val‖
      dsimp [r]
      linarith
    let a : C.Total := ⟨p.val.1.1, ⟨F.germRadiusCoordinate p.val r,
      (C.triangle p.val.1.1).edge_subset _
        (F.germRadiusCoordinate_mem_edge p.val positive small_p)⟩⟩
    let b : C.Total := ⟨q.val.1.1, ⟨F.germRadiusCoordinate q.val r,
      (C.triangle q.val.1.1).edge_subset _
        (F.germRadiusCoordinate_mem_edge q.val positive small_q)⟩⟩
    apply F.linkGerms_eq_or_mate_of_regular_spatial_point embedded (a := a) (b := b)
      (F.germRadiusCoordinate_not_vertex p.val positive small_p)
      ⟨rfl, F.germRadiusCoordinate_mem_edge p.val positive small_p⟩
      ⟨rfl, F.germRadiusCoordinate_mem_edge q.val positive small_q⟩
    change F.place p.val.1.1 (F.germRadiusCoordinate p.val r) =
      F.place q.val.1.1 (F.germRadiusCoordinate q.val r)
    rw [F.germRadiusCoordinate_spatial_unit, F.germRadiusCoordinate_spatial_unit,
      same_direction, F.linkGerm_apex Set.univ v p, F.linkGerm_apex Set.univ v q]
  · rintro (rfl | paired)
    · rfl
    · rw [← paired]
      exact (F.germUnitDirection_mate Set.univ p.val).symm

end Unfoldings.SpatialFolding
