module

public import Unfoldings.Source.SeamTransition
public import Unfoldings.Geometry.EdgePerfect

/-!
# Source-face hinge transitions also hold at retained seam endpoints

Both actual motions are locally constant along the retained edge. Every
edge neighborhood contains a nonvertex point, where the constructed hinge
transition is already proved. Thus the same motion identity holds at every
retained endpoint, including flat subdivision vertices.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceFaceMotion_seam :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (s : C.Seam)
      (q : (C.triangle (C.left s).face).Edge (C.left s).edge),
      ∀ left_outside : C.faceMap Set.univ (C.left s).face
          ((C.triangle (C.left s).face).edgeMap (C.left s).edge q) ∉ sourceCutLocus source,
        ∀ right_outside : C.faceMap Set.univ (C.right s).face
            ((C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s q)) ∉
              sourceCutLocus source,
          P.sourceFaceMotion R (C.right s).face
            ⟨(C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s q),
              right_outside⟩ =
          (C.seamHinge s).place.trans (P.sourceFaceMotion R (C.left s).face
            ⟨(C.triangle (C.left s).face).edgeMap (C.left s).edge q, left_outside⟩) := by
  let := P.metricSpace
  intro source R s q left_outside right_outside
  let l := (C.triangle (C.left s).face).edgeMap (C.left s).edge
  let r := fun z => (C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s z)
  let U : Set ((C.triangle (C.left s).face).Edge (C.left s).edge) :=
    {z | C.faceMap Set.univ (C.left s).face (l z) ∉ sourceCutLocus source}
  have continuous_l : Continuous l :=
    ((C.triangle (C.left s).face).edgeMap_isometry (C.left s).edge).continuous
  have continuous_r : Continuous r :=
    ((C.triangle (C.right s).face).edgeMap_isometry (C.right s).edge).continuous.comp
      (C.identify s).continuous
  have open_U : IsOpen U := (isClosed_sourceCutLocus source).isOpen_compl.preimage
    ((C.faceMap_lipschitz Set.univ (C.left s).face).continuous.comp continuous_l)
  have right_off (z : U) :
      C.faceMap Set.univ (C.right s).face (r z.val) ∉ sourceCutLocus source := by
    rw [← C.seam_identified Set.univ s (Set.mem_univ s)]
    exact z.property
  let left (z : U) : P.sourceFaceRegion source (C.left s).face := ⟨l z.val, z.property⟩
  let right (z : U) : P.sourceFaceRegion source (C.right s).face := ⟨r z.val, right_off z⟩
  have continuous_left : Continuous left :=
    (continuous_l.comp continuous_subtype_val).subtype_mk _
  have continuous_right : Continuous right :=
    (continuous_r.comp continuous_subtype_val).subtype_mk _
  let L := P.sourceFaceMotion R (C.left s).face ∘ left
  let M := P.sourceFaceMotion R (C.right s).face ∘ right
  have locally_L : IsLocallyConstant L :=
    (P.sourceFaceMotion_locallyConstant R (C.left s).face).comp_continuous continuous_left
  have locally_M : IsLocallyConstant M :=
    (P.sourceFaceMotion_locallyConstant R (C.right s).face).comp_continuous continuous_right
  let t : U := ⟨q, left_outside⟩
  let W : Set U := {z | L z = L t} ∩ {z | M z = M t}
  have open_W : IsOpen W := (locally_L.isOpen_fiber (L t)).inter (locally_M.isOpen_fiber (M t))
  have open_image : IsOpen (Subtype.val '' W) := open_U.isOpenMap_subtype_val W open_W
  have member : q ∈ Subtype.val '' W := ⟨t, ⟨rfl, rfl⟩, rfl⟩
  obtain ⟨z, ⟨u, in_W, rfl⟩, regular⟩ :=
    (C.triangle (C.left s).face).exists_nonvertex_in_edge_neighborhood (C.left s).edge
      q open_image member
  have actual := P.sourceFaceMotion_seam_nonvertex R s u.val regular u.property (right_off u)
  change M u = (C.seamHinge s).place.trans (L u) at actual
  change M t = (C.seamHinge s).place.trans (L t)
  rw [in_W.1, in_W.2] at actual
  exact actual

end Unfoldings.SpatialFolding.ConvexBoundary
