module

public import Unfoldings.Cap.RoofSections
public import Unfoldings.Cap.VerticalProduct
public import Mathlib.Topology.Order.Lattice

/-!
# The actual unbounded supporting-plane roof

The lower envelope of the original support planes gives an explicit entire
graph over the plane, homeomorphic to the plane. Its closed convex active-face
cells cover the plane and retain the original upward unit normal vectors.
This constructs the geometric extension, without assuming an acute skirt
triangulation, an outside cut forest, or a non-overlapping development.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem continuous_roofHeight : Continuous K.roofHeight := by
  let := K.nonempty_face
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun f _ => (K.supportHeight f).continuous_of_finiteDimensional)

/-- The complete planar cell on which an original support plane attains the roof. -/
def roofCell (f : Face) : Set Plane :=
  {p | ∀ g, K.supportHeight f p ≤ K.supportHeight g p}

theorem roofCell_eq_iInter (f : Face) :
    K.roofCell f = ⋂ g, {p | K.supportHeight f p ≤ K.supportHeight g p} := by
  ext p
  simp only [roofCell, Set.mem_ofPred_eq, Set.mem_iInter]

theorem isClosed_roofCell (f : Face) : IsClosed (K.roofCell f) := by
  rw [K.roofCell_eq_iInter]
  exact isClosed_iInter (fun g => isClosed_le
    (K.supportHeight f).continuous_of_finiteDimensional
    (K.supportHeight g).continuous_of_finiteDimensional)

theorem convex_roofCell (f : Face) : Convex ℝ (K.roofCell f) := by
  rw [K.roofCell_eq_iInter]
  apply convex_iInter
  intro g
  have rule := (convex_Iic (0 : ℝ)).affine_preimage (K.supportHeight f - K.supportHeight g)
  rw [AffineMap.coe_sub] at rule
  change Convex ℝ {p | K.supportHeight f p - K.supportHeight g p ≤ 0} at rule
  simpa only [sub_nonpos] using rule

theorem mem_roofCell_iff (f : Face) (p : Plane) :
    p ∈ K.roofCell f ↔ K.roofHeight p = K.supportHeight f p := by
  constructor
  · intro active
    obtain ⟨g, realizes⟩ := K.exists_roofHeight_eq_supportHeight p
    exact le_antisymm (K.roofHeight_le_supportHeight p f) (realizes ▸ active g)
  · intro active g
    rw [← active]
    exact K.roofHeight_le_supportHeight p g

theorem roofCells_cover (p : Plane) : ∃ f, p ∈ K.roofCell f := by
  obtain ⟨f, active⟩ := K.exists_roofHeight_eq_supportHeight p
  exact ⟨f, (K.mem_roofCell_iff f p).mpr active⟩

/-- The unbounded roof agrees with the supplied cap on every original face. -/
theorem projectFace_mem_roofCell (f : Face) (x : C.Cell f) :
    K.projectFace f x.val ∈ K.roofCell f := by
  rw [K.mem_roofCell_iff, K.roofHeight_face, K.supportHeight_face]

/-- The roof, with no footprint restriction. -/
def extendedRoof : Set Space := {z | z 2 = K.roofHeight (Cap.horizontal z)}

def roofPoint (p : Plane) : Space := Cap.horizontalAtHeight p (K.roofHeight p)

@[simp] theorem horizontal_roofPoint (p : Plane) : Cap.horizontal (K.roofPoint p) = p :=
  Cap.horizontal_horizontalAtHeight _ _

@[simp] theorem height_roofPoint (p : Plane) : K.roofPoint p 2 = K.roofHeight p := rfl

/-- The extension's graph point over an original face point is that same spatial point. -/
theorem roofPoint_projectFace (f : Face) (x : C.Cell f) :
    K.roofPoint (K.projectFace f x.val) = K.folding.place f x.val := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact K.roofHeight_face f x

theorem roofPoint_projectedVertex (v : C.Vertex Set.univ) :
    K.roofPoint (K.projectedVertex v) = K.folding.toSpace Set.univ (C.vertexPoint Set.univ v) := by
  obtain ⟨⟨f, i⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
  exact K.roofPoint_projectFace f ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i⟩

theorem continuous_roofPoint : Continuous K.roofPoint := by
  change Continuous (fun p => WithLp.toLp 2 ![p 0, p 1, K.roofHeight p])
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => by
      fin_cases i
      · exact (EuclideanSpace.proj 0).continuous
      · exact (EuclideanSpace.proj 1).continuous
      · exact K.continuous_roofHeight))

theorem roofPoint_mem (p : Plane) : K.roofPoint p ∈ K.extendedRoof := by
  simp only [extendedRoof, Set.mem_ofPred_eq, horizontal_roofPoint, height_roofPoint]

theorem roofPoint_horizontal (z : K.extendedRoof) : K.roofPoint (Cap.horizontal z.val) = z.val := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact z.property.symm

/-- Horizontal projection identifies the whole actual roof with the entire plane. -/
def roofHomeomorph : Plane ≃ₜ K.extendedRoof where
  toFun p := ⟨K.roofPoint p, K.roofPoint_mem p⟩
  invFun z := Cap.horizontal z.val
  left_inv p := K.horizontal_roofPoint p
  right_inv z := Subtype.ext (K.roofPoint_horizontal z)
  continuous_toFun := K.continuous_roofPoint.subtype_mk _
  continuous_invFun := Cap.horizontalCLM.continuous.comp continuous_subtype_val

theorem isClosed_extendedRoof : IsClosed K.extendedRoof := by
  exact isClosed_eq (EuclideanSpace.proj 2).continuous
    (K.continuous_roofHeight.comp Cap.horizontalCLM.continuous)

theorem original_surface_subset_extendedRoof : K.folding.surface ⊆ K.extendedRoof := by
  intro z member
  exact (K.surface_iff_roofHeight z).mp member |>.2

/-- Every point of the extension lies below every original upward support plane. -/
theorem roofPoint_support (p : Plane) (f : Face) :
    inner ℝ (K.normal f) (K.roofPoint p) ≤
      inner ℝ (K.normal f) (K.folding.place f 0) := by
  have height := K.roofHeight_le_supportHeight p f
  rw [supportHeight_apply, le_div_iff₀ (K.normal_upward f)] at height
  have split := Cap.horizontal_inner (K.normal f) (K.roofPoint p)
  rw [K.horizontal_roofPoint, K.height_roofPoint] at split
  linarith

end Unfoldings.ConvexCap
