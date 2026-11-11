module

public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Geometry.LineTransverse

/-!
# Actual seam vectors in projected, spatial, and developed coordinates

Both original incident faces pull a projected seam chord back to the same
spatial vector. Every retained seam has the same actual developed vector too.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The original left bank fixes one orientation of the actual projected seam vector. -/
def projectedSeamVector (s : C.Seam) : Plane :=
  K.projectFace (C.left s).face
      ((C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge)) -
    K.projectFace (C.left s).face ((C.triangle (C.left s).face).vertex (C.left s).edge)

theorem projectedSeamVector_ne_zero (s : C.Seam) : K.projectedSeamVector s ≠ 0 := by
  apply sub_ne_zero.mpr
  exact ((K.projectedTriangle (C.left s).face).edge_endpoints_ne (C.left s).edge).symm

/-- On the right face, the same vector uses the paired original endpoint order. -/
theorem projectedSeamVector_right (s : C.Seam) :
    K.projectedSeamVector s =
      K.projectFace (C.right s).face
        (C.identify s ((C.triangle (C.left s).face).endpoint (C.left s).edge true)).val -
      K.projectFace (C.right s).face
        (C.identify s ((C.triangle (C.left s).face).endpoint (C.left s).edge false)).val := by
  exact congrArg₂ (· - ·)
    (K.projectedTriangle_joined s ((C.triangle (C.left s).face).endpoint (C.left s).edge true))
    (K.projectedTriangle_joined s ((C.triangle (C.left s).face).endpoint (C.left s).edge false))

/-- Spatial seam directions agree even across an edge that will be cut. -/
theorem spatialDirection_seam (s : C.Seam) :
    K.spatialDirection (C.left s).face (K.projectedSeamVector s) =
      K.spatialDirection (C.right s).face (K.projectedSeamVector s) := by
  conv_lhs => unfold projectedSeamVector; rw [K.spatialDirection_chord]
  conv_rhs => rw [K.projectedSeamVector_right, K.spatialDirection_chord]
  exact congrArg₂ (· - ·)
    (K.folding.joined s ((C.triangle (C.left s).face).endpoint (C.left s).edge true))
    (K.folding.joined s ((C.triangle (C.left s).face).endpoint (C.left s).edge false))

/-- Vertex-avoiding section lines are transverse at every actual left-bank meeting. -/
theorem projectedSeamVector_transverse (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    {p q : Plane} (different : p ≠ q)
    (regular : ∀ t : ℝ, AffineMap.lineMap p q t ≠
      (K.projectedTriangle (C.left s).face).vertex (C.left s).edge)
    (t : ℝ) (meets : K.projectFace (C.left s).face x.val = AffineMap.lineMap p q t) :
    orient 0 (K.projectedSeamVector s) (q - p) ≠ 0 := by
  apply line_transverse_of_avoids_endpoint
    ((K.projectedTriangle (C.left s).face).edge_endpoints_ne (C.left s).edge)
    different regular t
  rw [← meets]
  apply orient_eq_zero_of_mem_segment
  change K.projectFace (C.left s).face x.val ∈
    (K.projectedTriangle (C.left s).face).edge (C.left s).edge
  rw [projectedTriangle, Triangle.affineImage_edge]
  exact ⟨x.val, x.property, rfl⟩

end Unfoldings.ConvexCap

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Retention identifies the two actual developed seam vectors with the original endpoint order. -/
theorem developedDirection_seam (s : C.Seam) (kept : s ∈ retain) :
    D.developedDirection K (C.left s).face (K.projectedSeamVector s) =
      D.developedDirection K (C.right s).face (K.projectedSeamVector s) := by
  conv_lhs => unfold ConvexCap.projectedSeamVector; rw [D.developedDirection_chord]
  conv_rhs => rw [K.projectedSeamVector_right, D.developedDirection_chord]
  exact congrArg₂ (· - ·)
    (D.joined s kept ((C.triangle (C.left s).face).endpoint (C.left s).edge true))
    (D.joined s kept ((C.triangle (C.left s).face).endpoint (C.left s).edge false))

end Unfoldings.FacewiseDevelopment
