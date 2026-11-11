module

public import Unfoldings.Cap.RadialForestDevelopment
public import Unfoldings.Cap.OutwardCutNeighbor
public import Unfoldings.Topology.ParentPaths
public import Unfoldings.Geometry.RadialChain
public import Unfoldings.Geometry.BankRadialOrder

/-! Whole-edge outward cut forests and radial control of their complete root paths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

namespace RadialCutForest

variable {K} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

/-- Every selected edge points outward for its entire length, with the same radial source. -/
def Outward : Prop :=
  ∀ w ∉ R.parents.roots, 0 ≤ inner ℝ (K.projectedVertex w - q)
    (K.projectedVertex (R.parents.parent w) - K.projectedVertex w)

def rootPath (w : C.Vertex Set.univ) : PolygonalChain Plane (R.parents.distanceToRoot w) where
  vertex i := K.projectedVertex (R.parents.parent^[i.val] w)

/-- The whole path, including the interiors of every fine seam, has increasing source distance. -/
theorem rootPath_radialFrom (outward : R.Outward) (w : C.Vertex Set.univ) :
    (R.rootPath w).RadialFrom q 0 := by
  intro i _earlier
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  change 0 ≤ inner ℝ (K.projectedVertex (R.parents.parent^[i.val] w) - q)
    (K.projectedVertex (R.parents.parent^[i.val + 1] w) -
      K.projectedVertex (R.parents.parent^[i.val] w))
  rw [Function.iterate_succ_apply']
  exact outward _ (R.parents.iterate_lt_distanceToRoot_not_mem w i.isLt)

/-- A concentric circle meets a constructed root path in at most one geometric point. -/
theorem rootPath_equal_radius (outward : R.Outward) (w : C.Vertex Set.univ)
    (i j : Fin (R.parents.distanceToRoot w)) (a b : unitInterval)
    (equal : dist q ((R.rootPath w).point i a) = dist q ((R.rootPath w).point j b)) :
    (R.rootPath w).point i a = (R.rootPath w).point j b := by
  rcases PolygonalChain.before_total i j a b with ordered | ordered
  · exact PolygonalChain.RadialFrom.point_eq_of_dist_eq (R.rootPath w)
      (R.rootPath_radialFrom outward w) i j a b (Nat.zero_le _) ordered equal
  · exact (PolygonalChain.RadialFrom.point_eq_of_dist_eq (R.rootPath w)
      (R.rootPath_radialFrom outward w) j i b a (Nat.zero_le _) ordered equal.symm).symm

end RadialCutForest

/-- Choose whole-edge outward seams while retaining the actual disk and development API. -/
def outwardRadialCutForest (q : Plane) (cuts : Set Plane)
    (progress : ∀ w : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ cuts →
        ∃ z s, C.seamGraph.IsLink s w z ∧
          dist q (K.projectedVertex w) < dist q (K.projectedVertex z) ∧
            (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ cuts ∧
              0 ≤ inner ℝ (K.projectedVertex w - q) (K.projectedVertex z - K.projectedVertex w)) :
    {R : K.RadialCutForest q cuts // R.Outward} := by
  classical
  let roots := {w : C.Vertex Set.univ |
    C.IsBoundaryVertex Set.univ w ∨ K.projectedVertex w ∉ cuts}
  have step (w : {w : C.Vertex Set.univ // w ∉ roots}) :=
    progress w.val (fun boundary => w.property (Or.inl boundary))
      (not_not.mp (fun outside => w.property (Or.inr outside)))
  choose next edge link farther supported outward using step
  let nextVertex (w : C.Vertex Set.univ) :=
    if nonroot : w ∉ roots then next ⟨w, nonroot⟩ else w
  let P : AscendingParents (C.Vertex Set.univ) :=
    { roots := roots
      parent := nextVertex
      height := fun w => dist q (K.projectedVertex w)
      fixed_root := fun w root => dite_eq_right (not_not.mpr root)
      ascending := fun w nonroot => by
        simp only [nextVertex, dite_eq_left nonroot]
        exact farther ⟨w, nonroot⟩ }
  let S : P.EdgeSelection C.seamGraph :=
    { edge := edge
      link := fun w => by
        have nonroot : w.val ∉ roots := w.property
        change C.seamGraph.IsLink _ w.val (nextVertex w.val)
        simp only [nextVertex, dite_eq_left nonroot]
        exact link w }
  let R : K.RadialCutForest q cuts := ⟨P, rfl, rfl, S, supported⟩
  refine ⟨R, ?_⟩
  intro w nonroot
  have unmarked : w ∉ roots := nonroot
  change 0 ≤ inner ℝ (K.projectedVertex w - q)
    (K.projectedVertex (nextVertex w) - K.projectedVertex w)
  simp only [nextVertex, dite_eq_left unmarked]
  exact outward ⟨w, unmarked⟩

end Unfoldings.ConvexCap
