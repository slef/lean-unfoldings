module

public import Unfoldings.Cone.CornerSector
public import Unfoldings.Cone.SectorReflection

/-!
# Corner coordinates following a chosen link direction

The Boolean orientation selects which incident edge is the initial ray.
Reflection in the sector bisector exchanges the rays when necessary.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle.CornerFrame

variable {T : Triangle} {i : Fin 3} (frame : T.CornerFrame i)

/-- The directed coordinates extend to a rigid motion of the whole ambient plane. -/
def directedPlace (reverse : Bool) : Plane ≃ᵃⁱ[ℝ] ℂ :=
  if reverse then frame.place.trans (sectorFlip (T.cornerAngle i)).toAffineIsometryEquiv
  else frame.place

def directedSectorIsometry (reverse : Bool) : T.cornerWedge i ≃ᵢ planarSector (T.cornerAngle i) :=
  if reverse then frame.sectorIsometry.trans (sectorFlipIsometry (T.cornerAngle i))
  else frame.sectorIsometry

theorem directedSectorIsometry_agrees (reverse : Bool) (x : T.cornerWedge i) :
    (frame.directedSectorIsometry reverse x).val = frame.directedPlace reverse x.val := by
  cases reverse <;> rfl

@[simp] theorem directedSectorIsometry_false (x : T.cornerWedge i) :
    (frame.directedSectorIsometry false x).val = frame.place x.val := rfl

@[simp] theorem directedSectorIsometry_true (x : T.cornerWedge i) :
    (frame.directedSectorIsometry true x).val =
      sectorFlip (T.cornerAngle i) (frame.place x.val) := rfl

/-- A point on the chosen initial bank has a nonnegative real coordinate. -/
theorem directed_initial_ray (reverse : Bool) (x : T.cornerWedge i)
    (boundary : if reverse then T.coord (Triangle.next i) x.val = 0
      else T.coord (Triangle.next (Triangle.next i)) x.val = 0) :
    ∃ r : ℝ, 0 ≤ r ∧ (frame.directedSectorIsometry reverse x).val = (r : ℂ) := by
  cases reverse
  · change T.coord (Triangle.next (Triangle.next i)) x.val = 0 at boundary
    let a := T.coord (Triangle.next i) x.val
    have expression : x.val = T.cornerCombination i a 0 := by
      have reconstruct := T.reconstruct_corner i x.val
      rw [boundary] at reconstruct
      exact reconstruct.symm
    refine ⟨a * dist (T.vertex i) (T.vertex (Triangle.next i)),
      mul_nonneg x.property.1 dist_nonneg, ?_⟩
    rw [frame.directedSectorIsometry_false, expression, frame.map_cornerCombination_polar]
    simp
  · change T.coord (Triangle.next i) x.val = 0 at boundary
    let b := T.coord (Triangle.next (Triangle.next i)) x.val
    have expression : x.val = T.cornerCombination i 0 b := by
      have reconstruct := T.reconstruct_corner i x.val
      rw [boundary] at reconstruct
      exact reconstruct.symm
    refine ⟨b * dist (T.vertex i) (T.vertex (Triangle.next (Triangle.next i))),
      mul_nonneg x.property.2 dist_nonneg, ?_⟩
    rw [frame.directedSectorIsometry_true, expression, frame.map_cornerCombination_polar]
    simp only [zero_mul, Complex.ofReal_zero, zero_add]
    rw [map_smul, sectorFlip_ray]
    simp [Complex.real_smul]

/-- A point on the other bank has a nonnegative terminal-ray coordinate. -/
theorem directed_terminal_ray (reverse : Bool) (x : T.cornerWedge i)
    (boundary : if reverse then T.coord (Triangle.next (Triangle.next i)) x.val = 0
      else T.coord (Triangle.next i) x.val = 0) :
    ∃ r : ℝ, 0 ≤ r ∧
      (frame.directedSectorIsometry reverse x).val = r • polarRay (T.cornerAngle i) := by
  cases reverse
  · change T.coord (Triangle.next i) x.val = 0 at boundary
    let b := T.coord (Triangle.next (Triangle.next i)) x.val
    have expression : x.val = T.cornerCombination i 0 b := by
      have reconstruct := T.reconstruct_corner i x.val
      rw [boundary] at reconstruct
      exact reconstruct.symm
    refine ⟨b * dist (T.vertex i) (T.vertex (Triangle.next (Triangle.next i))),
      mul_nonneg x.property.2 dist_nonneg, ?_⟩
    rw [frame.directedSectorIsometry_false, expression, frame.map_cornerCombination_polar]
    simp only [zero_mul, Complex.ofReal_zero, zero_add]
  · change T.coord (Triangle.next (Triangle.next i)) x.val = 0 at boundary
    let a := T.coord (Triangle.next i) x.val
    have expression : x.val = T.cornerCombination i a 0 := by
      have reconstruct := T.reconstruct_corner i x.val
      rw [boundary] at reconstruct
      exact reconstruct.symm
    refine ⟨a * dist (T.vertex i) (T.vertex (Triangle.next i)),
      mul_nonneg x.property.1 dist_nonneg, ?_⟩
    rw [frame.directedSectorIsometry_true, expression, frame.map_cornerCombination_polar]
    simp only [zero_mul, zero_smul, add_zero]
    have cast : ((a * dist (T.vertex i) (T.vertex (Triangle.next i)) : ℝ) : ℂ) =
        (a * dist (T.vertex i) (T.vertex (Triangle.next i))) • (1 : ℂ) := by
      simp [Complex.real_smul]
    rw [cast, map_smul, sectorFlip_one]

@[simp] theorem directedSectorIsometry_apex (reverse : Bool) :
    (frame.directedSectorIsometry reverse
      ⟨T.vertex i, T.vertex_mem_cornerWedge i⟩).val = 0 := by
  cases reverse <;> simp [frame.apex]

theorem norm_directedSectorIsometry (reverse : Bool) (x : T.cornerWedge i) :
    ‖(frame.directedSectorIsometry reverse x).val‖ = dist (T.vertex i) x.val := by
  have equal := (frame.directedSectorIsometry reverse).isometry.dist_eq
    ⟨T.vertex i, T.vertex_mem_cornerWedge i⟩ x
  change dist (frame.directedSectorIsometry reverse
    ⟨T.vertex i, T.vertex_mem_cornerWedge i⟩).val
      (frame.directedSectorIsometry reverse x).val = dist (T.vertex i) x.val at equal
  rwa [frame.directedSectorIsometry_apex, dist_zero_left] at equal

/-- The initial bank coordinate is its actual metric radius. -/
theorem directed_initial_radius (reverse : Bool) (x : T.cornerWedge i)
    (boundary : if reverse then T.coord (Triangle.next i) x.val = 0
      else T.coord (Triangle.next (Triangle.next i)) x.val = 0) :
    (frame.directedSectorIsometry reverse x).val = (dist (T.vertex i) x.val : ℂ) := by
  obtain ⟨r, nonnegative, equal⟩ := frame.directed_initial_ray reverse x boundary
  have norm := frame.norm_directedSectorIsometry reverse x
  rw [equal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonnegative] at norm
  exact equal.trans (congrArg Complex.ofReal norm)

/-- The terminal bank coordinate has its actual metric radius and genuine corner heading. -/
theorem directed_terminal_radius (reverse : Bool) (x : T.cornerWedge i)
    (boundary : if reverse then T.coord (Triangle.next (Triangle.next i)) x.val = 0
      else T.coord (Triangle.next i) x.val = 0) :
    (frame.directedSectorIsometry reverse x).val =
      dist (T.vertex i) x.val • polarRay (T.cornerAngle i) := by
  obtain ⟨r, nonnegative, equal⟩ := frame.directed_terminal_ray reverse x boundary
  have norm := frame.norm_directedSectorIsometry reverse x
  rw [equal, norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative,
    norm_polarRay, mul_one] at norm
  rwa [norm] at equal

end Unfoldings.Triangle.CornerFrame
