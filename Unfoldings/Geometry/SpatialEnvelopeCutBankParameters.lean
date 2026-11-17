module

public import Unfoldings.Polyhedron.CutBankParameters
public import Unfoldings.Geometry.SpatialEnvelopeDirectedBanks

/-! Both sides of an original cut edge keep its projected segment and endpoint coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance cutBankParameterIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (retain : Set T.pairedComplex.Seam)

/-- Either cut-bank label projects into the same original left-edge segment. -/
theorem horizontal_cutBank_mem_left_edge (s : T.pairedComplex.CutSeam retain) (side : Bool)
    (q : (T.pairedComplex.triangle (T.pairedComplex.cutBank retain s side).val.face).Edge
      (T.pairedComplex.cutBank retain s side).val.edge) :
    Cap.horizontal (T.pairedFolding.toSpace retain
      (T.pairedComplex.bankMap retain (T.pairedComplex.cutBank retain s side) q)) ∈
      (T.projectedTriangle (T.pairedComplex.left s.val).face).edge
        (T.pairedComplex.left s.val).edge := by
  have position := (congrArg Cap.horizontal
    (T.pairedFolding.toSpace_cutBank_left_parameter retain s side q)).trans
      ((family (T.support (T.pairedComplex.left s.val).face)).horizontal_place _)
  exact position ▸ (T.edgeProjection _ _
    (T.pairedComplex.cutBankLeftParameterEquiv retain s side q)).property

/-- An endpoint on either actual cut bank is one of the two original projected endpoints. -/
theorem horizontal_cutBank_endpoint (s : T.pairedComplex.CutSeam retain) (side : Bool)
    (q : (T.pairedComplex.triangle (T.pairedComplex.cutBank retain s side).val.face).Edge
      (T.pairedComplex.cutBank retain s side).val.edge)
    (vertex : (T.pairedComplex.triangle (T.pairedComplex.cutBank retain s side).val.face).IsVertex
      q.val) :
    Cap.horizontal (T.pairedFolding.toSpace retain
      (T.pairedComplex.bankMap retain (T.pairedComplex.cutBank retain s side) q)) =
        (T.projectedTriangle (T.pairedComplex.left s.val).face).vertex
          (T.pairedComplex.left s.val).edge ∨
    Cap.horizontal (T.pairedFolding.toSpace retain
      (T.pairedComplex.bankMap retain (T.pairedComplex.cutBank retain s side) q)) =
        (T.projectedTriangle (T.pairedComplex.left s.val).face).vertex
          (Triangle.next (T.pairedComplex.left s.val).edge) := by
  have position := (congrArg Cap.horizontal
    (T.pairedFolding.toSpace_cutBank_left_parameter retain s side q)).trans
      ((family (T.support (T.pairedComplex.left s.val).face)).horizontal_place _)
  have is_vertex := (T.project_isVertex_iff (T.pairedComplex.left s.val).face _).mpr
    ((T.pairedComplex.cutBankLeftParameter_isVertex_iff retain s side q).mpr vertex)
  have ends := ((T.projectedTriangle (T.pairedComplex.left s.val).face).edge_vertex_iff
    (T.pairedComplex.left s.val).edge
    (T.edgeProjection _ _ (T.pairedComplex.cutBankLeftParameterEquiv retain s side q))).mp is_vertex
  exact ends.imp (position.trans ·) (position.trans ·)

end Unfoldings.SpatialEnvelope.Triangulation
