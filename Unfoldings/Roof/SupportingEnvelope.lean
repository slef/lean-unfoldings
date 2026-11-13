module

public import Unfoldings.Roof.AcuteProjection
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Arbitrary-rim roofs as lower envelopes of supporting planes

The input support inequalities imply a concave polyhedral roof. The roof is
defined on the whole horizontal plane and agrees with every actual cap face.
No claim that its extension has no new vertices is made here.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

include K in
theorem nonempty_face : Nonempty Face := by
  obtain ⟨p, present⟩ := K.interior_projection
  obtain ⟨z, face, _⟩ := interior_subset present
  obtain ⟨f, _⟩ := Set.mem_iUnion.mp face
  exact ⟨f⟩

/-- The affine height of an actual supporting plane, solved using its positive vertical normal. -/
def supportHeight (f : Face) : Plane →ᵃ[ℝ] ℝ :=
  (K.normal f 2)⁻¹ •
    (AffineMap.const ℝ Plane (inner ℝ (K.normal f) (K.folding.place f 0)) -
      (innerSL ℝ (Cap.horizontal (K.normal f))).toLinearMap.toAffineMap)

@[simp] theorem supportHeight_apply (f : Face) (p : Plane) :
    K.supportHeight f p =
      (inner ℝ (K.normal f) (K.folding.place f 0) -
        inner ℝ (Cap.horizontal (K.normal f)) p) / K.normal f 2 := by
  simp [supportHeight, div_eq_mul_inv, mul_comm]

theorem supportHeight_face (f : Face) (x : Plane) :
    K.supportHeight f (K.projectFace f x) = K.folding.place f x 2 := by
  rw [supportHeight_apply, div_eq_iff (K.normal_upward f).ne']
  have tangent := K.normal_tangent_chord f x 0
  rw [inner_sub_right] at tangent
  have split := Cap.horizontal_inner (K.normal f) (K.folding.place f x)
  change inner ℝ (K.normal f) (K.folding.place f x) =
    inner ℝ (Cap.horizontal (K.normal f)) (K.projectFace f x) +
      K.normal f 2 * K.folding.place f x 2 at split
  linarith

theorem face_height_le_supportHeight (f g : Face) (x : C.Cell g) :
    K.folding.place g x.val 2 ≤ K.supportHeight f (K.projectFace g x.val) := by
  rw [supportHeight_apply, le_div_iff₀ (K.normal_upward f)]
  have support := K.supporting f g x
  rw [inner_sub_right] at support
  have split := Cap.horizontal_inner (K.normal f) (K.folding.place g x.val)
  change inner ℝ (K.normal f) (K.folding.place g x.val) =
    inner ℝ (Cap.horizontal (K.normal f)) (K.projectFace g x.val) +
      K.normal f 2 * K.folding.place g x.val 2 at split
  linarith

/-- The finite lower envelope is meaningful everywhere, including outside the footprint. -/
def roofHeight (p : Plane) : ℝ :=
  let := K.nonempty_face
  Finset.univ.inf' Finset.univ_nonempty (fun f => K.supportHeight f p)

theorem roofHeight_le_supportHeight (p : Plane) (f : Face) :
    K.roofHeight p ≤ K.supportHeight f p := by
  let := K.nonempty_face
  change Finset.univ.inf' Finset.univ_nonempty (fun g => K.supportHeight g p) ≤ K.supportHeight f p
  exact Finset.inf'_le _ (Finset.mem_univ f)

theorem exists_roofHeight_eq_supportHeight (p : Plane) :
    ∃ f, K.roofHeight p = K.supportHeight f p := by
  let := K.nonempty_face
  obtain ⟨f, _, equal⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun f => K.supportHeight f p)
  exact ⟨f, equal⟩

/-- All actual face heights, including their boundaries, are exactly the roof heights. -/
theorem roofHeight_face (f : Face) (x : C.Cell f) :
    K.roofHeight (K.projectFace f x.val) = K.folding.place f x.val 2 := by
  apply le_antisymm
  · exact (K.roofHeight_le_supportHeight _ f).trans_eq (K.supportHeight_face f x.val)
  · obtain ⟨g, equal⟩ := K.exists_roofHeight_eq_supportHeight (K.projectFace f x.val)
    rw [equal]
    exact K.face_height_le_supportHeight g f x

/-- Convexity of the cap roof follows from the actual supporting inequalities. -/
theorem roofHeight_concave : ConcaveOn ℝ Set.univ K.roofHeight := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb sum
  obtain ⟨f, equal⟩ := K.exists_roofHeight_eq_supportHeight (a • x + b • y)
  rw [equal, Convex.combo_affine_apply sum]
  exact add_le_add (smul_le_smul_of_nonneg_left (K.roofHeight_le_supportHeight x f) ha)
    (smul_le_smul_of_nonneg_left (K.roofHeight_le_supportHeight y f) hb)

/-- Exact graph description over the actual footprint. -/
theorem surface_iff_roofHeight (z : Space) :
    z ∈ K.folding.surface ↔
      Cap.horizontal z ∈ K.footprint ∧ z 2 = K.roofHeight (Cap.horizontal z) := by
  constructor
  · intro present
    obtain ⟨f, x, carrier, equal⟩ := Set.mem_iUnion.mp present
    refine ⟨⟨z, present, rfl⟩, ?_⟩
    subst z
    exact (K.roofHeight_face f ⟨x, carrier⟩).symm
  · rintro ⟨⟨w, present, projection⟩, height⟩
    have wheight : w 2 = K.roofHeight (Cap.horizontal w) := by
      obtain ⟨f, x, carrier, equal⟩ := Set.mem_iUnion.mp present
      subst w
      exact (K.roofHeight_face f ⟨x, carrier⟩).symm
    have equal : z = w := by
      ext i
      fin_cases i
      · exact (congrArg (fun p : Plane => p 0) projection).symm
      · exact (congrArg (fun p : Plane => p 1) projection).symm
      · change z 2 = w 2
        rw [height, wheight, projection]
    exact equal.symm ▸ present

end Unfoldings.ConvexRoof
