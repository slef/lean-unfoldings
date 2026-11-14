module

public import Unfoldings.Convex.FiniteDualFace
public import Unfoldings.Roof.GradientSelection
public import Unfoldings.Roof.OriginalFaceHeight

/-! The clipped conjugate of the actual lifted original roof vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

def dualPoint (corner : Face × Fin 3) : Plane :=
  K.projectFace corner.1 ((C.triangle corner.1).vertex corner.2)

def dualLevel (corner : Face × Fin 3) : ℝ :=
  -K.folding.place corner.1 ((C.triangle corner.1).vertex corner.2) 2

/-- The finite conjugate uses only the actual original lifted vertices. -/
def dualCost (p : Plane) : ℝ :=
  let := K.nonempty_face
  FiniteDual.cost K.dualPoint K.dualLevel p

/-- The convex extension has height opposite to the spatial roof height. -/
def clippedExtension (slopes : Set Plane) (compact : IsCompact slopes)
    (nonempty : slopes.Nonempty) : SlopeEnvelope :=
  let := K.nonempty_face
  FiniteDual.clipped K.dualPoint K.dualLevel slopes compact nonempty

theorem supportHeight_gradient (f : Face) (p : Plane) :
    K.supportHeight f p = K.supportHeight f 0 - inner ℝ p (K.normalSlope f) := by
  have difference := K.supportHeight_sub f 0 p
  simp only [sub_zero] at difference
  have comm : inner ℝ (K.normalSlope f) p = inner ℝ p (K.normalSlope f) :=
    real_inner_comm _ _
  rw [comm] at difference
  linarith

theorem dual_face_support (f : Face) (corner : Face × Fin 3) :
    inner ℝ (K.dualPoint corner) (K.normalSlope f) - K.supportHeight f 0 ≤
      K.dualLevel corner := by
  have bound := K.face_height_le_supportHeight f corner.1
    ⟨(C.triangle corner.1).vertex corner.2, (C.triangle corner.1).vertex_mem corner.2⟩
  rw [K.supportHeight_gradient] at bound
  change inner ℝ (K.projectFace corner.1 ((C.triangle corner.1).vertex corner.2))
    (K.normalSlope f) - K.supportHeight f 0 ≤
      -K.folding.place corner.1 ((C.triangle corner.1).vertex corner.2) 2
  linarith

theorem dual_face_contact (f : Face) (i : Fin 3) :
    K.dualLevel (f, i) = inner ℝ (K.dualPoint (f, i)) (K.normalSlope f) -
      K.supportHeight f 0 := by
  have equal := K.supportHeight_face f ((C.triangle f).vertex i)
  rw [K.supportHeight_gradient] at equal
  change -K.folding.place f ((C.triangle f).vertex i) 2 =
    inner ℝ (K.projectFace f ((C.triangle f).vertex i)) (K.normalSlope f) - K.supportHeight f 0
  linarith

/-- The full original triangle is contained in its primal supporting face. -/
theorem projectedTriangle_subset_dualFace (f : Face) :
    (K.projectedTriangle f).carrier ⊆
      FiniteDual.face K.dualPoint K.dualLevel (K.normalSlope f) (-K.supportHeight f 0) := by
  apply convexHull_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨(f, i), rfl, K.dual_face_contact f i⟩

/-- Every selected original whole triangle retains its exact actual spatial graph height. -/
theorem clippedExtension_preserves_original_face {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) (f : Face)
    (selected : K.normalSlope f ∈ slopes) {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier) :
    (K.clippedExtension slopes compact nonempty).height p = -K.roofHeight p := by
  let := K.nonempty_face
  have equal := FiniteDual.clipped_preserves_face K.dualPoint K.dualLevel compact nonempty
    (s := K.normalSlope f) (c := -K.supportHeight f 0)
    (fun i => K.dual_face_support f i) ⟨(f, 0), K.dual_face_contact f 0⟩ selected
    (K.projectedTriangle_subset_dualFace f member)
  change (K.clippedExtension slopes compact nonempty).height p =
    inner ℝ p (K.normalSlope f) + -K.supportHeight f 0 at equal
  rw [K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f member,
    K.supportHeight_gradient]
  linarith

/-- The slope of every preserved original face is active at all its closed points. -/
theorem clippedExtension_original_face_active {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) (f : Face)
    (selected : K.normalSlope f ∈ slopes) {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier) :
    (K.clippedExtension slopes compact nonempty).Active p (K.normalSlope f) := by
  let := K.nonempty_face
  refine ⟨selected, ?_⟩
  rw [K.clippedExtension_preserves_original_face compact nonempty f selected member,
    K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f member]
  change -K.supportHeight f p = inner ℝ p (K.normalSlope f) -
    FiniteDual.cost K.dualPoint K.dualLevel (K.normalSlope f)
  rw [FiniteDual.cost_at_support K.dualPoint K.dualLevel
    (c := -K.supportHeight f 0) (fun i => K.dual_face_support f i)
    ⟨(f, 0), K.dual_face_contact f 0⟩, K.supportHeight_gradient]
  ring

/-- For an interior selected slope the equality domain is exactly the original supporting
face. Coplanar input subdivisions remain included in that same physical supporting face. -/
theorem clippedExtension_eq_original_plane_iff {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) (f : Face)
    (selected : K.normalSlope f ∈ interior slopes) (p : Plane) :
    (K.clippedExtension slopes compact nonempty).height p = -K.supportHeight f p ↔
      p ∈ FiniteDual.face K.dualPoint K.dualLevel (K.normalSlope f) (-K.supportHeight f 0) := by
  let := K.nonempty_face
  have exact_domain := FiniteDual.clipped_eq_plane_iff K.dualPoint K.dualLevel compact nonempty
    (s := K.normalSlope f) (x := p) (c := -K.supportHeight f 0)
    (fun i => K.dual_face_support f i) ⟨(f, 0), K.dual_face_contact f 0⟩ selected
  change (FiniteDual.clipped K.dualPoint K.dualLevel slopes compact nonempty).height p =
    -K.supportHeight f p ↔ _
  rw [K.supportHeight_gradient]
  have identity : -(K.supportHeight f 0 - inner ℝ p (K.normalSlope f)) =
      inner ℝ p (K.normalSlope f) + -K.supportHeight f 0 := by ring
  rw [identity]
  exact exact_domain

end Unfoldings.ConvexRoof
