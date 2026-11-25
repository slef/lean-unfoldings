module

public import Unfoldings.FewestNets.ThreeExitOriginalFaceLift
public import Unfoldings.FewestNets.ThreeExitMesh
public import Unfoldings.Roof.AffineFloorPhysicalCut

/-! The finite three-exit forest cut has the exact physical metric within its affine floor. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "G₀" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "G" => SlopeEnvelope.recenter (G₀) B.reference
local notation "floor" => SlopeEnvelope.FiniteSlopeModel.referenceFloor B.reference

variable (level : ℝ)
  (M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel)

local notation "T[" higher "]" => R.fineMesh level M higher
local notation "F[" higher "]" => R.fineMeshForest level M higher
local notation "cuts[" higher "]" => FiniteEmbeddedGraph.carrier (R.truncatedEmbedding level higher)
local notation "initial" => fineMeshCutFirst (K := K) (slopes := slopes) (seed := seed)
local notation "terminal" => R.fineMeshCutLast level
local notation "sectionFootprint" => SpatialEnvelope.clipAbove M.plane floor (-level)

local instance fineCutIndexFintype (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[higher]).Index := @Fintype.ofFinite _ (T[higher]).finite

/-- The finite and complete cut carriers agree throughout the closed true section. -/
theorem fineCut_mem_iff_whole (higher : ∀ v : V, (G).height (p v) < level) {x : Plane}
    (member : x ∈ sectionFootprint) : x ∈ cuts[higher] ↔ x ∈ R.wholeCarrier := by
  rw [← R.wholeCarrier_inter_sublevel higher, Set.mem_inter_iff, and_iff_left]
  rwa [M.clipAbove_referenceFloor_eq] at member

private theorem fineCut_edge_aligned (higher : ∀ v : V, (G).height (p v) < level)
    (f : (T[higher]).Index) (e : Fin 3) (x : ((T[higher]).projectedTriangle f).Edge e)
    (regular : ¬ ((T[higher]).projectedTriangle f).IsVertex x.val)
    (cut : x.val ∈ R.wholeCarrier) :
    ((T[higher]).projectedTriangle f).edge e ⊆ R.wholeCarrier := by
  have window (y : Plane) (member : y ∈ ((T[higher]).projectedTriangle f).edge e) :
      y ∈ sectionFootprint :=
    (T[higher]).cover.symm.subset
      (Set.mem_iUnion.mpr ⟨f, ((T[higher]).projectedTriangle f).edge_subset e member⟩)
  have finite_cut := (R.fineCut_mem_iff_whole level M higher (window _ x.property)).mpr cut
  rw [R.fineMesh_cuts_eq_segments level higher] at finite_cut
  have all := (T[higher]).prescribed_cut_aligned initial terminal
    (fun i => R.fineMeshCutEndpoints_ne level i higher) f e x regular finite_cut
  rw [← R.fineMesh_cuts_eq_segments level higher] at all
  intro y member
  exact (R.fineCut_mem_iff_whole level M higher (window y member)).mp (all member)

theorem fineMesh_disjoint_wholeCut_interior (higher : ∀ v : V, (G).height (p v) < level)
    (f : (T[higher]).Index) :
    Disjoint (interior ((T[higher]).projectedTriangle f).carrier) R.wholeCarrier := by
  have disjoint := (T[higher]).prescribed_cut_disjoint_interior initial terminal
    (fun i => R.fineMeshCutEndpoints_ne level i higher) f
  rw [← R.fineMesh_cuts_eq_segments level higher] at disjoint
  apply Set.disjoint_left.mpr
  intro x in_triangle on_cut
  have inside : x ∈ sectionFootprint :=
    (T[higher]).cover.symm.subset (Set.mem_iUnion.mpr ⟨f, interior_subset in_triangle⟩)
  exact Set.disjoint_left.mp disjoint in_triangle
    ((R.fineCut_mem_iff_whole level M higher inside).mpr on_cut)

theorem fineMesh_retain_eq_wholeCut (higher : ∀ v : V, (G).height (p v) < level) :
    (F[higher]).retain = (T[higher]).retainOutside R.wholeCarrier := by
  rw [R.fineMesh_retain_eq_prescribed level M higher]
  ext s
  change (¬ _ ⊆ cuts[higher]) ↔ (¬ _ ⊆ R.wholeCarrier)
  apply not_congr
  have mem_win (x : Plane) (member : x ∈ ((T[higher]).projectedTriangle
      ((T[higher]).pairedComplex.left s).face).edge ((T[higher]).pairedComplex.left s).edge) :
      x ∈ sectionFootprint :=
    (T[higher]).cover.symm.subset (Set.mem_iUnion.mpr
      ⟨_, ((T[higher]).projectedTriangle _).edge_subset _ member⟩)
  exact ⟨fun included x hx => (R.fineCut_mem_iff_whole level M higher (mem_win x hx)).mp (included hx),
    fun included x hx => (R.fineCut_mem_iff_whole level M higher (mem_win x hx)).mpr (included hx)⟩

theorem fineMesh_removed_edge (higher : ∀ v : V, (G).height (p v) < level)
    (s : (T[higher]).pairedComplex.Seam) (removed : s ∉ (F[higher]).retain)
    (x : ((T[higher]).pairedComplex.triangle ((T[higher]).pairedComplex.left s).face).Edge
      ((T[higher]).pairedComplex.left s).edge) :
    Cap.horizontal ((T[higher]).placement ((T[higher]).pairedComplex.left s).face x.val) ∈
      R.wholeCarrier := by
  apply (T[higher]).removed_edge_mem_cut R.wholeCarrier s _ x
  rwa [← R.fineMesh_retain_eq_wholeCut level M higher]

theorem fineMesh_retained_open_edge (higher : ∀ v : V, (G).height (p v) < level)
    (s : (T[higher]).pairedComplex.Seam) (kept : s ∈ (F[higher]).retain) :
    Disjoint ((T[higher]).pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' R.wholeCarrier) := by
  apply (T[higher]).retained_openSeamImage_disjoint R.wholeCarrier
    (R.fineCut_edge_aligned level M higher) s
  rwa [← R.fineMesh_retain_eq_wholeCut level M higher]

/-- The exact finite cut, including every original vertex copy, is isometric
to the affine-floor graph patch cut by the original whole carrier. -/
def fineMeshWholeGraphEquiv (higher : ∀ v : V, (G).height (p v) < level) :
    (T[higher]).pairedComplex.Realization (F[higher]).retain ≃ᵢ
      (T[higher]).graphPartition.Cut R.wholeCarrier :=
  (T[higher]).pairedCutGraphEquiv (F[higher]).retain R.wholeCarrier
    (R.fineMesh_removed_edge level M higher) (R.fineMesh_retained_open_edge level M higher)

theorem fold_fineMeshWholeGraphEquiv (higher : ∀ v : V, (G).height (p v) < level)
    (x : (T[higher]).pairedComplex.Realization (F[higher]).retain) :
    (T[higher]).graphPartition.fold R.wholeCarrier (R.fineMeshWholeGraphEquiv level M higher x) =
      (T[higher]).pairedFolding.toSpace (F[higher]).retain x :=
  (T[higher]).fold_pairedCutGraphEquiv (F[higher]).retain R.wholeCarrier
    (R.fineMesh_removed_edge level M higher) (R.fineMesh_retained_open_edge level M higher) x

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
