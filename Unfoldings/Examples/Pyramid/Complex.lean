module

public import Unfoldings.Examples.Pyramid.Coordinates
public import Unfoldings.Complex.Folding

/-! The actual four radial seam pairings of the concrete diamond pyramid. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Pyramid

/-- A seam is named by its axis and the sign of its boundary endpoint. -/
def left : Bool × Bool → EdgeRef (Bool × Bool)
  | (false, s) => ⟨(s, false), 0⟩
  | (true, s) => ⟨(false, s), 2⟩

def right : Bool × Bool → EdgeRef (Bool × Bool)
  | (false, s) => ⟨(s, true), 0⟩
  | (true, s) => ⟨(true, s), 2⟩

def identify (s : Bool × Bool) : triangle.Edge (left s).edge ≃ᵢ triangle.Edge (right s).edge := by
  obtain ⟨axis, s⟩ := s
  cases axis <;> exact IsometryEquiv.refl _

def complex : TriangleComplex (Bool × Bool) where
  triangle _ := triangle
  Seam := Bool × Bool
  left := left
  right := right
  distinct := by rintro ⟨a, b⟩; cases a <;> cases b <;> decide
  identify := identify
  unique := by
    rintro ⟨a, b⟩ ⟨c, d⟩ shared
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [left, right]

/-- Both endpoints of each paired radial edge have exactly the same spatial placement. -/
theorem paired_vertices (s : Bool × Bool) :
    placement (left s).face (triangle.vertex (left s).edge) =
        placement (right s).face (triangle.vertex (left s).edge) ∧
      placement (left s).face (triangle.vertex (Triangle.next (left s).edge)) =
        placement (right s).face (triangle.vertex (Triangle.next (left s).edge)) := by
  simp only [placement_vertex]
  obtain ⟨axis, s⟩ := s
  cases axis <;> simp [left, right, vertex, Triangle.next]

theorem identify_joined (s : Bool × Bool) (x : triangle.Edge (left s).edge) :
    placement (left s).face x.val = placement (right s).face (identify s x).val := by
  have value : (identify s x).val = x.val := by
    obtain ⟨axis, s⟩ := s
    cases axis <;> rfl
  rw [value]
  obtain ⟨t, _, at_x⟩ := (segment_eq_image_lineMap ℝ
    (triangle.vertex (left s).edge)
    (triangle.vertex (Triangle.next (left s).edge))).subset x.property
  have first := (paired_vertices s).1
  have last := (paired_vertices s).2
  change (placement (left s).face).toAffineMap x.val =
    (placement (right s).face).toAffineMap x.val
  rw [← at_x, AffineMap.apply_lineMap, AffineMap.apply_lineMap]
  exact congrArg₂ (fun a b : Space => AffineMap.lineMap a b t) first last

def folding : SpatialFolding complex where
  place := placement
  joined := identify_joined

end Unfoldings.Examples.Pyramid
