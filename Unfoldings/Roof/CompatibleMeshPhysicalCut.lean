module

public import Unfoldings.Roof.CompatibleMeshRetention
public import Unfoldings.Roof.TruncatedWholeCarrier
public import Unfoldings.Geometry.PrescribedCutMetric

/-! The constructed compatible forest mesh has the actual whole-forest cut metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleMeshPhysicalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


/-- In this actual mesh every nonvertex edge contact with the bounded cut is a full cut edge. -/
theorem compatibleMesh_truncated_cut_aligned (f : (T).Index) (e : Fin 3)
    (x : ((T).projectedTriangle f).Edge e) (regular : ¬ ((T).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ R.truncatedCarrier level higher) :
    ((T).projectedTriangle f).edge e ⊆ R.truncatedCarrier level higher := by
  let S : SpatialEnvelope.ConstrainedTriangulation M.plane
      (segmentEquations (R.cutFirst level) (R.cutLast level higher)
        (K.cut_endpoints_ne compact nonempty R no_boundary level higher)) (-level) := {
    toTriangulation := (T).toTriangulation
    signs j k := (T).signs j (.inr k)
    constrained j p hp k := (T).constrained j p hp (.inr k) }
  rw [R.truncatedCarrier_eq_segments level higher] at member ⊢
  exact S.prescribed_cut_aligned _ _ _ f e x regular member

/-- On the actual closed finite mesh, the bounded and whole cuts agree pointwise. -/
theorem compatibleMesh_cut_agree {p : Plane} (member : p ∈ SpatialEnvelope.clip M.plane (-level)) :
    p ∈ R.truncatedCarrier level higher ↔ p ∈ R.carrier :=
  R.mem_truncatedCarrier_iff level higher (by
    rw [M.clip_eq_sublevel, neg_neg] at member
    exact member)

/-- Actual whole cut contacts force entire fine edges to be cut. -/
theorem compatibleMesh_whole_cut_aligned (f : (T).Index) (e : Fin 3)
    (x : ((T).projectedTriangle f).Edge e) (regular : ¬ ((T).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ R.carrier) : ((T).projectedTriangle f).edge e ⊆ R.carrier := by
  have in_clip (p : Plane) (hp : p ∈ ((T).projectedTriangle f).edge e) :
      p ∈ SpatialEnvelope.clip M.plane (-level) :=
    (T).cover.symm.subset (Set.mem_iUnion.mpr ⟨f, ((T).projectedTriangle f).edge_subset e hp⟩)
  have bounded := K.compatibleMesh_truncated_cut_aligned compact nonempty R no_boundary
    level higher M positive inner_disk f e x regular
    ((K.compatibleMesh_cut_agree compact nonempty R level higher M
      (in_clip x.val x.property)).mpr member)
  intro p hp
  exact (K.compatibleMesh_cut_agree compact nonempty R level higher M
    (in_clip p hp)).mp (bounded hp)

/-- The whole original cut avoids every actual fine triangle interior. -/
theorem compatibleMesh_cut_disjoint_interior (f : (T).Index) :
    Disjoint (interior ((T).projectedTriangle f).carrier) R.carrier := by
  let S : SpatialEnvelope.ConstrainedTriangulation M.plane
      (segmentEquations (R.cutFirst level) (R.cutLast level higher)
        (K.cut_endpoints_ne compact nonempty R no_boundary level higher)) (-level) := {
    toTriangulation := (T).toTriangulation
    signs j k := (T).signs j (.inr k)
    constrained j p hp k := (T).constrained j p hp (.inr k) }
  have disjoint := S.prescribed_cut_disjoint_interior _ _ _ f
  rw [← R.truncatedCarrier_eq_segments level higher] at disjoint
  apply Set.disjoint_left.mpr
  intro p in_triangle member
  have in_clip : p ∈ SpatialEnvelope.clip M.plane (-level) :=
    (T).cover.symm.subset (Set.mem_iUnion.mpr ⟨f, interior_subset in_triangle⟩)
  exact Set.disjoint_left.mp disjoint in_triangle
    ((K.compatibleMesh_cut_agree compact nonempty R level higher M in_clip).mpr member)

/-- The constructed fine forest removes precisely the whole mesh edges in the full original cut. -/
theorem compatibleMesh_retain_eq_whole_prescribed :
    (Fcut).retain = (T).toTriangulation.retainOutside R.carrier := by
  rw [K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher M
    positive inner_disk beta acute]
  ext s
  change (¬ _ ⊆ R.truncatedCarrier level higher) ↔ (¬ _ ⊆ R.carrier)
  apply not_congr
  constructor
  · intro selected p hp
    exact (R.truncatedCarrier_eq_carrier_inter_sublevel level higher).subset (selected hp) |>.1
  · intro selected p hp
    apply (K.compatibleMesh_cut_agree compact nonempty R level higher M ?_).mpr (selected hp)
    exact (T).cover.symm.subset (Set.mem_iUnion.mpr
      ⟨(T).pairedComplex.left s |>.face,
        ((T).projectedTriangle ((T).pairedComplex.left s).face).edge_subset _ hp⟩)

/-- Every removed original closed fine edge lies in the actual whole forest cut. -/
theorem compatibleMesh_removed_edge (s : (T).pairedComplex.Seam) (removed : s ∉ (Fcut).retain)
    (x : ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge) :
    Cap.horizontal ((T).placement ((T).pairedComplex.left s).face x.val) ∈ R.carrier := by
  apply (T).toTriangulation.removed_edge_mem_cut R.carrier s ?_ x
  rwa [← K.compatibleMesh_retain_eq_whole_prescribed compact nonempty R no_boundary
    level higher M positive inner_disk beta acute]

/-- Every retained open fine edge avoids the full original cut, including all terminal rays. -/
theorem compatibleMesh_retained_open_edge (s : (T).pairedComplex.Seam) (kept : s ∈ (Fcut).retain) :
    Disjoint ((T).pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' R.carrier) := by
  apply (T).toTriangulation.retained_openSeamImage_disjoint R.carrier
    (K.compatibleMesh_whole_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk) s
  rwa [← K.compatibleMesh_retain_eq_whole_prescribed compact nonempty R no_boundary
    level higher M positive inner_disk beta acute]

/-- The original constructed finite forest cut is isometric to the actual triangular physical
cut by the full forest. No metric, fan or retained-edge placement hypotheses remain. -/
def compatibleMeshWholeGraphEquiv :
    (T).pairedComplex.Realization (Fcut).retain ≃ᵢ
      (T).toTriangulation.graphPartition.Cut R.carrier :=
  (T).toTriangulation.pairedCutGraphEquiv conforming (Fcut).retain R.carrier
    (K.compatibleMesh_removed_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute)
    (K.compatibleMesh_retained_open_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute)

/-- The actual finite-to-whole physical cut identification retains the original spatial fold. -/
theorem fold_compatibleMeshWholeGraphEquiv (x : (T).pairedComplex.Realization (Fcut).retain) :
    (T).toTriangulation.graphPartition.fold R.carrier
      (K.compatibleMeshWholeGraphEquiv compact nonempty R no_boundary level higher M
        positive inner_disk beta acute x) = (T).pairedFolding.toSpace (Fcut).retain x :=
  (T).toTriangulation.fold_pairedCutGraphEquiv conforming (Fcut).retain R.carrier
    (K.compatibleMesh_removed_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute)
    (K.compatibleMesh_retained_open_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute) x

end Unfoldings.ConvexRoof
