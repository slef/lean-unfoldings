module

public import Unfoldings.Polyhedron.Closedness
public import Unfoldings.Complex.FaceRestrictionMap
public import Unfoldings.Complex.CollapsedCutCarrier
public import Unfoldings.Complex.IntrinsicBoundary
public import Mathlib.Analysis.Normed.Module.Connected

/-! Boundary images of whole-face subregions in a closed triangulation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (U : Set Face)

open Classical in
/-- The uncut restriction to these original triangles is an intrinsic disk. -/
def RestrictionIsDisk : Prop :=
  Nonempty ((C.restrictFaces U).Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1)

open Classical in
/-- The bank boundary of a whole-face subregion mapped back to the uncut surface. -/
def selectedFaceBoundary : Set (C.Realization Set.univ) :=
  C.includeRestricted U Set.univ '' (C.restrictFaces U).bankBoundary Set.univ

open Classical in
/-- A local edge of a selected face is a boundary bank precisely when the
triangle across its original seam is excluded. -/
theorem restrictFaces_isBoundaryEdge_iff (s : C.Seam) (b : Bool)
    (selected : (C.seamSide s b).face ∈ U) :
    (C.restrictFaces U).IsBoundaryEdge Set.univ
        ⟨⟨(C.seamSide s b).face, selected⟩, (C.seamSide s b).edge⟩ ↔
      (C.seamSide s (!b)).face ∉ U := by
  let D := C.restrictFaces U
  let e : EdgeRef U := ⟨⟨(C.seamSide s b).face, selected⟩, (C.seamSide s b).edge⟩
  constructor
  · intro boundary opposite
    have both : (C.left s).face ∈ U ∧ (C.right s).face ∈ U := by
      cases b
      · exact ⟨selected, opposite⟩
      · exact ⟨opposite, selected⟩
    let t : D.Seam := ⟨s, both⟩
    apply boundary
    cases b
    · exact ⟨t, Set.mem_univ _, Or.inl rfl⟩
    · exact ⟨t, Set.mem_univ _, Or.inr rfl⟩
  · intro opposite
    rintro ⟨t, _, attached⟩
    obtain ⟨a, side⟩ : ∃ a : Bool, D.seamSide t a = e := by
      rcases attached with h | h
      · exact ⟨false, h.symm⟩
      · exact ⟨true, h.symm⟩
    have same : C.seamSide t.val a = C.seamSide s b := by
      have h := congrArg (fun e : EdgeRef U => (⟨e.face.val, e.edge⟩ : EdgeRef Face)) side
      cases a <;> exact h
    have pair : (t.val, a) = (s, b) := C.seamSide_injective same
    have st : t.val = s := congrArg Prod.fst pair
    apply opposite
    cases b
    · exact st ▸ t.property.2
    · exact st ▸ t.property.1

open Classical in
/-- Every point on a seam between a selected and an excluded face is
in the image of the selected disk's bank boundary. -/
theorem seamSide_mem_selectedFaceBoundary (s : C.Seam) (b : Bool)
    (selected : (C.seamSide s b).face ∈ U) (excluded : (C.seamSide s (!b)).face ∉ U)
    (y : (C.triangle (C.seamSide s b).face).Edge (C.seamSide s b).edge) :
    C.faceMap Set.univ (C.seamSide s b).face
        ((C.triangle (C.seamSide s b).face).edgeMap (C.seamSide s b).edge y) ∈
      C.selectedFaceBoundary U := by
  let D := C.restrictFaces U
  let bank : D.BoundaryBank Set.univ :=
    ⟨_, (C.restrictFaces_isBoundaryEdge_iff U s b selected).mpr excluded⟩
  exact ⟨D.bankMap Set.univ bank y, D.bankMap_mem_bankBoundary Set.univ bank y, rfl⟩

open Classical in
/-- In a closed triangulation every selected boundary bank is one side of
an original seam whose other face is excluded. -/
theorem exists_original_seam_of_selected_boundary_bank
    {F : SpatialFolding C} (P : F.ConvexBoundary)
    (bank : (C.restrictFaces U).BoundaryBank Set.univ) :
    ∃ (s : C.Seam) (b : Bool) (selected : (C.seamSide s b).face ∈ U),
      ∃ excluded : (C.seamSide s (!b)).face ∉ U,
        bank = ⟨⟨⟨(C.seamSide s b).face, selected⟩, (C.seamSide s b).edge⟩,
          (C.restrictFaces_isBoundaryEdge_iff U s b selected).mpr excluded⟩ := by
  let e : EdgeRef Face := ⟨bank.val.face.val, bank.val.edge⟩
  obtain ⟨s, b, side⟩ := P.exists_seam_at_edge e
  have face : (C.seamSide s b).face = bank.val.face.val := congrArg EdgeRef.face side
  have index : (C.seamSide s b).edge = bank.val.edge := congrArg EdgeRef.edge side
  have selected : (C.seamSide s b).face ∈ U := face.symm ▸ bank.val.face.property
  have ref : (⟨⟨(C.seamSide s b).face, selected⟩, (C.seamSide s b).edge⟩ : EdgeRef U) =
      bank.val := by
    calc
      _ = ⟨bank.val.face, bank.val.edge⟩ :=
        congrArg₂ EdgeRef.mk (Subtype.ext face) index
      _ = _ := by cases bank.val; rfl
  have excluded := (C.restrictFaces_isBoundaryEdge_iff U s b selected).mp (ref.symm ▸ bank.property)
  exact ⟨s, b, selected, excluded, Subtype.ext ref.symm⟩

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

open Classical in
include F in
/-- A selected intrinsic disk has a connected boundary image in the uncut surface. -/
theorem isConnected_selectedFaceBoundary (U : Set Face)
    (disk : (C.restrictFaces U).Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1) :
    IsConnected (C.selectedFaceBoundary U) := by
  let f : Metric.sphere (0 : Plane) 1 → (C.restrictFaces U).Realization Set.univ :=
    disk.symm ∘ unitSphereDiskInclusion
  have range_eq : Set.range f = (C.restrictFaces U).bankBoundary Set.univ := by
    ext x
    rw [(F.restrictFaces U).bankBoundary_iff_disk_norm_eq_one Set.univ disk x]
    constructor
    · rintro ⟨z, rfl⟩
      change ‖(disk (disk.symm (unitSphereDiskInclusion z))).val‖ = 1
      rw [disk.apply_symm_apply]
      exact mem_sphere_zero_iff_norm.mp z.property
    · intro h
      let z : Metric.sphere (0 : Plane) 1 :=
        ⟨(disk x).val, mem_sphere_zero_iff_norm.mpr h⟩
      exact ⟨z, disk.symm_apply_apply x⟩
  have dim : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  let : ConnectedSpace (Metric.sphere (0 : Plane) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere dim 0 zero_le_one)
  have connected := isConnected_range (disk.symm.continuous.comp unitSphereDiskInclusion.continuous)
  change IsConnected (Set.range f) at connected
  rw [range_eq] at connected
  exact connected.image _ (C.includeRestricted_lipschitz U Set.univ).continuous.continuousOn

end Unfoldings.SpatialFolding
