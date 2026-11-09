module

public import Unfoldings.Polyhedron.FigureHeadings
public import Unfoldings.Cone.AngularOverlap

/-!
# The actual central fan makes exactly one full turn

The normalized endpoints identify every developed sector interior with a
positive cone over the corresponding actual figure edge. Their proved
separation forces total angle at most one turn. The closing ray and positive
total angle then force exactly one turn, rather than an arbitrary winding.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

theorem figureCentralFan_interior_pullback
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) {z : ℂ}
    (inside : z ∈ interior ((P.figureCentralFan V c closes).faceImage i)) :
    (P.figureDevelopFrame V c closes).symm z ∈
      positiveRadialHull (openSegment ℝ (V.linkPolygon c i)
        (V.linkPolygon c (finRotate (n + 1) i))) := by
  let A := P.figureCentralFan V c closes
  let L := P.figureDevelopFrame V c closes
  let h := (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph
  change z ∈ interior (h '' planarSector (A.angle i)) at inside
  rw [← h.image_interior] at inside
  obtain ⟨w, hw, mapped⟩ := inside
  rw [interior_planarSector (A.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  change polarRay (A.heading i.castSucc) * ((a : ℂ) + b • polarRay (A.angle i)) = z at mapped
  have first_pos : 0 < ‖V.linkPolygon c i‖ := norm_pos_iff.mpr (P.linkPolygon_ne_zero V c i)
  have second_pos : 0 < ‖V.linkPolygon c (finRotate (n + 1) i)‖ :=
    norm_pos_iff.mpr (P.linkPolygon_ne_zero V c _)
  rw [positiveRadialHull_openSegment]
  refine ⟨a / ‖V.linkPolygon c i‖, div_pos ha first_pos,
    b / ‖V.linkPolygon c (finRotate (n + 1) i)‖, div_pos hb second_pos, ?_⟩
  apply L.injective
  rw [L.apply_symm_apply, map_add, map_smul, map_smul,
    P.figureDevelopFrame_heading, P.figureDevelopFrame_heading_finish]
  have cancel_first : ((a / ‖V.linkPolygon c i‖ : ℝ) : ℂ) *
      (‖V.linkPolygon c i‖ : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ first_pos.ne']
  have cancel_second : ((b / ‖V.linkPolygon c (finRotate (n + 1) i)‖ : ℝ) : ℂ) *
      (‖V.linkPolygon c (finRotate (n + 1) i)‖ : ℂ) = (b : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ second_pos.ne']
  change z = (a / ‖V.linkPolygon c i‖) • ((‖V.linkPolygon c i‖ : ℂ) *
    polarRay (A.heading i.castSucc)) +
    (b / ‖V.linkPolygon c (finRotate (n + 1) i)‖) •
      ((‖V.linkPolygon c (finRotate (n + 1) i)‖ : ℂ) * polarRay (A.heading i.succ))
  rw [Complex.real_smul, Complex.real_smul, ← mul_assoc, ← mul_assoc,
    cancel_first, cancel_second, A.heading_succ, polarRay_add, ← mapped]
  rw [Complex.real_smul]
  ring

theorem figureCentralFan_nonoverlapping
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    (P.figureCentralFan V c closes).Nonoverlapping := by
  intro i j different
  apply Set.disjoint_left.mpr
  intro z hi hj
  have first := P.figureCentralFan_interior_pullback V c closes i hi
  have second := P.figureCentralFan_interior_pullback V c closes j hj
  exact Set.disjoint_left.mp (P.linkPolygon_positiveRadial_disjoint V c closes different)
    first (positiveRadialHull_mono (openSegment_subset_segment ℝ _ _) second)

theorem figureCentralFan_full_turn
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    (P.figureCentralFan V c closes).totalAngle = 2 * Real.pi := by
  let A := P.figureCentralFan V c closes
  have upper := A.nonoverlapping_iff_totalAngle_le.mp (P.figureCentralFan_nonoverlapping V c closes)
  have circle : Circle.exp A.totalAngle = 1 := by
    apply Subtype.ext
    exact P.figureCentralFan_outer_ray V c closes
  obtain ⟨k, turns⟩ := Circle.exp_eq_one.mp circle
  have positive : 0 < (k : ℝ) := by nlinarith [A.totalAngle_pos, Real.pi_pos]
  have bound : (k : ℝ) ≤ 1 := by nlinarith [Real.pi_pos]
  have integer_positive : 0 < k := by exact_mod_cast positive
  have integer_bound : k ≤ 1 := by exact_mod_cast bound
  have one : k = 1 := by omega
  rw [one] at turns
  simpa only [Int.cast_one, one_mul] using turns

end Unfoldings.SpatialFolding.ConvexBoundary
