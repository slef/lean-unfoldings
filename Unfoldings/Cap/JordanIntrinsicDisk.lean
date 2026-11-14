module

public import Unfoldings.Cap.JordanFaceSelection
public import Unfoldings.Roof.CapBridge
public import Unfoldings.Roof.SelectionIntrinsicDisk

/-! The actual selected whole-face Jordan filling is an intrinsic disk with injective projection. -/

@[expose] public section

noncomputable section


namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
theorem jordanFaces_nonempty : (K.jordanFaces J).Nonempty := by
  obtain ⟨p, inside⟩ := PlanarTopology.interior_closedJordanDomain_nonempty jordan
  have covered := interior_subset inside
  rw [K.jordanDomain_eq_projectedFace_union jordan contains avoids] at covered
  obtain ⟨f, hf, _⟩ := Set.mem_iUnion₂.mp covered
  exact ⟨f, hf⟩

include jordan contains avoids in
open Classical in
theorem jordanFaces_roof_carrier :
    K.toRoof.restrictedCarrier (K.jordanFaces J) = PlanarTopology.closedJordanDomain J := by
  change (⋃ f : {f : Face // f ∈ K.jordanFaces J}, (K.projectedTriangle f.val).carrier) = _
  rw [K.jordanDomain_eq_projectedFace_union jordan contains avoids]
  ext p
  simp only [Set.mem_iUnion, Subtype.exists, exists_prop]

include jordan contains avoids in
open Classical in
theorem jordanFaces_roof_frontier :
    Schoenflies.IsJordanCurve (frontier (K.toRoof.restrictedCarrier (K.jordanFaces J))) := by
  rw [K.jordanFaces_roof_carrier jordan contains avoids,
    PlanarTopology.frontier_closedJordanDomain jordan]
  exact jordan

open Classical in
/-- All intrinsic vertex classes retain exactly their actual geometric projections. -/
def jordanIntrinsicHomeomorph :
    (C.restrictFaces (K.jordanFaces J)).Realization Set.univ ≃ₜ
      PlanarTopology.closedJordanDomain J :=
  (K.toRoof.restrictProjectionHomeomorph (K.jordanFaces J)
    (K.jordanFaces_nonempty jordan contains avoids)
    (K.jordanFaces_roof_frontier jordan contains avoids)).trans
    (Homeomorph.setCongr (K.jordanFaces_roof_carrier jordan contains avoids))

open Classical in
@[simp] theorem jordanIntrinsicHomeomorph_apply
    (x : (C.restrictFaces (K.jordanFaces J)).Realization Set.univ) :
    (K.jordanIntrinsicHomeomorph jordan contains avoids x).val =
      K.toRoof.restrictProjection (K.jordanFaces J) x := rfl

open Classical in
/-- Construct the actual cut-metric whole-face filling as a closed disk. -/
def jordanIntrinsicDisk :
    (C.restrictFaces (K.jordanFaces J)).Realization Set.univ ≃ₜ
      Metric.closedBall (0 : Plane) 1 := by
  let F := Classical.choose (PlanarTopology.exists_ambient_closedJordanDomain_disk jordan)
  have image := Classical.choose_spec
    (PlanarTopology.exists_ambient_closedJordanDomain_disk jordan)
  exact (K.jordanIntrinsicHomeomorph jordan contains avoids).trans
    ((F.image (PlanarTopology.closedJordanDomain J)).trans (Homeomorph.setCongr image))

end Unfoldings.ConvexCap
