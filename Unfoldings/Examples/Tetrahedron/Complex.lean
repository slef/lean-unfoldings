module

public import Unfoldings.Examples.Tetrahedron.Faces
public import Unfoldings.Geometry.EdgeIdentification

/-! The six genuine paired edges and rigid spatial folding of the tetrahedron. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

def left : Fin 6 → EdgeRef (Fin 4) :=
  ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨2, 0⟩]

def right : Fin 6 → EdgeRef (Fin 4) :=
  ![⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨3, 2⟩, ⟨3, 0⟩]

def reverse : Fin 6 → Bool := ![false, true, false, false, true, false]

def endpointLabel (edge : EdgeRef (Fin 4)) (b : Bool) : Fin 4 :=
  corner edge.face (if b then Triangle.next edge.edge else edge.edge)

theorem matching_labels (s : Fin 6) (b : Bool) :
    endpointLabel (left s) b = endpointLabel (right s) (Bool.xor b (reverse s)) := by
  fin_cases s <;> cases b <;> decide

theorem placement_endpoint (e : EdgeRef (Fin 4)) (b : Bool) :
    placement e.face ((triangle e.face).endpoint e.edge b).val = vertex (endpointLabel e b) := by
  cases b <;> exact placement_vertex _ _

theorem edge_length (s : Fin 6) :
    dist ((triangle (left s).face).vertex (left s).edge)
      ((triangle (left s).face).vertex (Triangle.next (left s).edge)) =
    dist ((triangle (right s).face).endpoint (right s).edge (reverse s)).val
      ((triangle (right s).face).endpoint (right s).edge (!(reverse s))).val := by
  change dist ((triangle (left s).face).endpoint (left s).edge false).val
    ((triangle (left s).face).endpoint (left s).edge true).val = _
  rw [← (placement (left s).face).isometry.dist_eq,
    ← (placement (right s).face).isometry.dist_eq,
    placement_endpoint, placement_endpoint, placement_endpoint, placement_endpoint]
  have first := matching_labels s false
  have last := matching_labels s true
  simpa only [Bool.false_xor, Bool.true_xor] using
    congrArg₂ (fun a b => dist (vertex a) (vertex b)) first last

def identify (s : Fin 6) :=
  (triangle (left s).face).edgeIdentification (triangle (right s).face)
    (left s).edge (right s).edge (reverse s) (edge_length s)

abbrev complex : TriangleComplex (Fin 4) where
  triangle := triangle
  Seam := Fin 6
  left := left
  right := right
  distinct := by intro s; fin_cases s <;> decide
  identify := identify
  unique := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all [left, right]

theorem identify_joined (s : Fin 6)
    (x : (triangle (left s).face).Edge (left s).edge) :
    placement (left s).face x.val = placement (right s).face (identify s x).val := by
  let motion := (triangle (left s).face).edgeMotion (triangle (right s).face)
    (left s).edge (right s).edge (reverse s)
  let lhs := (placement (left s).face).toAffineMap
  let rhs := (placement (right s).face).toAffineMap.comp motion.toAffineEquiv.toAffineMap
  have ends (b : Bool) :
      lhs ((triangle (left s).face).endpoint (left s).edge b).val =
        rhs ((triangle (left s).face).endpoint (left s).edge b).val := by
    have labels := matching_labels s b
    cases b
    · change placement (left s).face ((triangle (left s).face).vertex (left s).edge) =
        placement (right s).face (motion ((triangle (left s).face).vertex (left s).edge))
      rw [Triangle.edgeMotion_first, placement_endpoint, placement_vertex]
      simpa only [endpointLabel, Bool.false_xor, Bool.true_xor, Bool.false_eq_true,
        ite_false, ite_true] using congrArg vertex labels
    · change placement (left s).face
        ((triangle (left s).face).vertex (Triangle.next (left s).edge)) =
        placement (right s).face
          (motion ((triangle (left s).face).vertex (Triangle.next (left s).edge)))
      rw [Triangle.edgeMotion_last _ _ _ _ _ (edge_length s),
        placement_endpoint, placement_vertex]
      simpa only [endpointLabel, Bool.false_xor, Bool.true_xor, Bool.false_eq_true,
        ite_false, ite_true] using congrArg vertex labels
  have member := x.property
  change x.val ∈ segment ℝ ((triangle (left s).face).vertex (left s).edge)
    ((triangle (left s).face).vertex (Triangle.next (left s).edge)) at member
  rw [segment_eq_image_lineMap] at member
  obtain ⟨t, _ht, equal⟩ := member
  change lhs x.val = rhs x.val
  have first : lhs ((triangle (left s).face).vertex (left s).edge) =
      rhs ((triangle (left s).face).vertex (left s).edge) := ends false
  have last : lhs ((triangle (left s).face).vertex (Triangle.next (left s).edge)) =
      rhs ((triangle (left s).face).vertex (Triangle.next (left s).edge)) := ends true
  rw [← equal, lhs.apply_lineMap, rhs.apply_lineMap, first, last]

def folding : SpatialFolding complex where
  place := placement
  joined := identify_joined

theorem face_pair (f g : Fin 4) (different : f ≠ g) :
    ∃ s, (left s).face = f ∧ (right s).face = g ∨ (left s).face = g ∧ (right s).face = f := by
  fin_cases f <;> fin_cases g <;>
    simp_all [left, right, Fin.exists_fin_succ]

theorem opposite_label (s : Fin 6) :
    corner (left s).face (Triangle.next (Triangle.next (left s).edge)) = (right s).face := by
  fin_cases s <;> decide

end Unfoldings.Examples.Tetrahedron
