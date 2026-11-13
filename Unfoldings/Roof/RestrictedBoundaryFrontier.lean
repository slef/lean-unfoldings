module

public import Unfoldings.Roof.RestrictedBoundaryJordan
public import Unfoldings.Geometry.EdgeParameters
public import Unfoldings.Geometry.TriangleFrontier

/-! The actual bank boundary of a whole-face roof restriction projects into its frontier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- The whole closed projected faces of a face restriction. -/
def restrictedCarrier (U : Set Face) : Set Plane :=
  ⋃ f : {f : Face // f ∈ U}, (K.projectedTriangle f.val).carrier

open Classical in
theorem compact_restrictedCarrier (U : Set Face) : IsCompact (K.restrictedCarrier U) :=
  isCompact_iUnion fun f => (K.projectedTriangle f.val).compact_carrier

open Classical in
/-- A projected nonvertex bank point belongs to exactly its own restricted face. -/
theorem restricted_bank_face_unique (U : Set Face)
    (bank : (C.restrictFaces U).BoundaryBank Set.univ)
    (x : ((C.restrictFaces U).triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face.val).IsVertex x.val)
    (g : {f : Face // f ∈ U})
    (member : K.projectFace bank.val.face.val x.val ∈ (K.projectedTriangle g.val).carrier) :
    g = bank.val.face := by
  let R := C.restrictFaces U
  rw [projectedTriangle, Triangle.affineImage_carrier] at member
  obtain ⟨y, hy, image⟩ := member
  have intrinsic := K.restrictProjection_fiber_regular U bank.val.face
    ((R.triangle bank.val.face).edgeMap bank.val.edge x) regular
    (R.faceMap Set.univ g ⟨y, hy⟩) image.symm
  have tagged := (R.bankMap_eq_iff Set.univ bank x regular ⟨g, ⟨y, hy⟩⟩).mp intrinsic
  exact (congrArg Sigma.fst tagged).symm

open Classical in
theorem restricted_bank_regular_mem_frontier (U : Set Face)
    (bank : (C.restrictFaces U).BoundaryBank Set.univ)
    (x : ((C.restrictFaces U).triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face.val).IsVertex x.val) :
    K.projectFace bank.val.face.val x.val ∈ frontier (K.restrictedCarrier U) := by
  let f := bank.val.face
  let p := K.projectFace f.val x.val
  let others := ⋃ g : {g : {f : Face // f ∈ U} // g ≠ f},
    (K.projectedTriangle g.val.val).carrier
  have closed : IsClosed others :=
    (isCompact_iUnion fun (g : {g : {f : Face // f ∈ U} // g ≠ f}) =>
      (K.projectedTriangle g.val.val).compact_carrier).isClosed
  have excluded : p ∉ others := by
    rintro member
    obtain ⟨g, inside⟩ := Set.mem_iUnion.mp member
    exact g.property (K.restricted_bank_face_unique U bank x regular g.val inside)
  have in_face : p ∈ (K.projectedTriangle f.val).carrier := by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨x.val, (C.triangle f.val).edge_subset bank.val.edge x.property, rfl⟩
  have on_edge : p ∈ (K.projectedTriangle f.val).edge bank.val.edge := by
    rw [projectedTriangle, Triangle.affineImage_edge]
    exact ⟨x.val, x.property, rfl⟩
  apply (mem_frontier_iff_notMem_interior (Set.mem_iUnion.mpr ⟨f, in_face⟩)).mpr
  intro inside
  have neighborhood : K.restrictedCarrier U ∩ othersᶜ ∈ nhds p :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp inside) (closed.isOpen_compl.mem_nhds excluded)
  have contained : K.restrictedCarrier U ∩ othersᶜ ⊆ (K.projectedTriangle f.val).carrier := by
    rintro q ⟨member, outside⟩
    obtain ⟨g, in_g⟩ := Set.mem_iUnion.mp member
    by_cases same : g = f
    · simpa only [same] using in_g
    · exact (outside (Set.mem_iUnion.mpr ⟨⟨g, same⟩, in_g⟩)).elim
  have interior_face : p ∈ interior (K.projectedTriangle f.val).carrier :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset neighborhood contained)
  exact Set.disjoint_left.mp disjoint_interior_frontier interior_face
    ((K.projectedTriangle f.val).edge_subset_frontier bank.val.edge on_edge)

open Classical in
/-- All points of each actual bank segment, including its endpoints, lie on the frontier. -/
theorem restricted_bank_mem_frontier (U : Set Face)
    (bank : (C.restrictFaces U).BoundaryBank Set.univ)
    (x : ((C.restrictFaces U).triangle bank.val.face).Edge bank.val.edge) :
    K.projectFace bank.val.face.val x.val ∈ frontier (K.restrictedCarrier U) := by
  let R := C.restrictFaces U
  let T := R.triangle bank.val.face
  let point := fun t : ℝ => K.projectFace bank.val.face.val
    (AffineMap.lineMap (T.vertex bank.val.edge) (T.vertex (Triangle.next bank.val.edge)) t)
  have continuous : Continuous point := by
    exact (K.projectFace bank.val.face.val).continuous_of_finiteDimensional.comp
      (show ℝ →ᵃ[ℝ] Plane from AffineMap.lineMap (T.vertex bank.val.edge)
        (T.vertex (Triangle.next bank.val.edge))).continuous_of_finiteDimensional
  have regular_points : Set.Ioo (0 : ℝ) 1 ⊆ point ⁻¹' frontier (K.restrictedCarrier U) := by
    intro t ht
    exact K.restricted_bank_regular_mem_frontier U bank
      ⟨_, lineMap_mem_segment ℝ _ _ ⟨ht.1.le, ht.2.le⟩⟩
      (T.lineMap_edge_not_vertex bank.val.edge ht)
  have all_points : Set.Icc (0 : ℝ) 1 ⊆ point ⁻¹' frontier (K.restrictedCarrier U) := by
    rw [← closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    exact closure_minimal regular_points (isClosed_frontier.preimage continuous)
  obtain ⟨t, equal⟩ := R.bankParameter_surjective Set.univ bank x
  have image := all_points t.property
  have coordinates := congrArg Subtype.val equal
  change AffineMap.lineMap (T.vertex bank.val.edge)
    (T.vertex (Triangle.next bank.val.edge)) t.val = x.val at coordinates
  change K.projectFace bank.val.face.val
    (AffineMap.lineMap (T.vertex bank.val.edge)
      (T.vertex (Triangle.next bank.val.edge)) t.val) ∈ frontier (K.restrictedCarrier U) at image
  rwa [coordinates] at image

open Classical in
/-- The projected intrinsic bank set is contained in the geometric frontier, even at pinches. -/
theorem restricted_boundary_subset_frontier (U : Set Face) :
    K.restrictProjection U '' (C.restrictFaces U).bankBoundary Set.univ ⊆
      frontier (K.restrictedCarrier U) := by
  rintro p ⟨y, member, rfl⟩
  obtain ⟨bank, x, rfl⟩ := Set.mem_iUnion.mp member
  exact K.restricted_bank_mem_frontier U bank x

open Classical in
/-- Every nonempty intrinsic bank set supplies an actual Jordan subcurve of the frontier. -/
theorem exists_Jordan_restricted_frontier (U : Set Face)
    (bank : (C.restrictFaces U).BoundaryBank Set.univ) :
    ∃ J : Set Plane, Schoenflies.IsJordanCurve J ∧ J ⊆ frontier (K.restrictedCarrier U) := by
  obtain ⟨J, jordan, subset⟩ := K.exists_restricted_boundary_Jordan U bank
  exact ⟨J, jordan, subset.trans (K.restricted_boundary_subset_frontier U)⟩

end Unfoldings.ConvexRoof
