module

public import Unfoldings.FewestNets.IcosahedronGuardedSeparation
public import Unfoldings.FewestNets.VoronoiNetwork

/-! Only the local corner bounds remain to construct the actual Voronoi network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

def meshCornerAngle {q : ℕ} (hq : 0 < q) (t : MeshFace q) (j k : Fin 3) : ℝ :=
  angle (minorArcTangent (facetNormal hq t) (facetNormal hq (adjacentFace hq t j)))
    (minorArcTangent (facetNormal hq t) (facetNormal hq (adjacentFace hq t k)))

theorem meshCornerAngle_comm {q : ℕ} (hq : 0 < q) (t : MeshFace q) (j k : Fin 3) :
    meshCornerAngle hq t j k = meshCornerAngle hq t k j :=
  angle_comm _ _

theorem cornerGuardAltitude_comm {q : ℕ} (o : Orientation ℝ Plane (Fin 2))
    (hq : 0 < q) (t : MeshFace q) (j k : Fin 3) :
    cornerGuardAltitude o hq t j k = cornerGuardAltitude o hq t k j := by
  rw [cornerGuardAltitude, cornerGuardAltitude, o.areaForm_swap, abs_neg,
    norm_sub_rev (adjacentSlope hq t k) (adjacentSlope hq t j)]

theorem exists_edgeOpposite_eq_of_incident {q : ℕ} (hq : 0 < q) (t : MeshFace q)
    (e : MeshEdge q) (he : EdgeIncident e t) : ∃ j : Fin 3, edgeOpposite hq t j = e := by
  obtain ⟨j, matched⟩ := (faceIncidentEquivCorners hq t).symm.surjective ⟨e, he⟩
  exact ⟨j, congrArg Subtype.val matched⟩

theorem meshEndpoint_other_eq_of_corner {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (j : Fin 3) (a : Bool)
    (central : meshEndpoint hq (edgeOpposite hq t j) a = facetNormal hq t) :
    meshEndpoint hq (edgeOpposite hq t j) (!a) = facetNormal hq (adjacentFace hq t j) := by
  let e := edgeOpposite hq t j
  let b := oppositeEndpointIndex hq t e
  have other : meshEndpoint hq e b = facetNormal hq (adjacentFace hq t j) :=
    meshEndpoint_eq_facetNormal_incidentFace hq e b
  have flags : a = (!b) ∨ a = b := by cases a <;> cases b <;> decide
  rcases flags with ok | bad
  · rw [ok, Bool.not_not]
    exact other
  · have eq := ((congrArg (meshEndpoint hq e) bad).symm.trans central)
    exact (adjacentFace_ne qbig hq t j (facetNormal_injective qbig hq (other.symm.trans eq))).elim

/-- The local altitude and angle certificates suffice for the actual indexed Voronoi network. -/
theorem voronoiNetwork_of_corner_bounds {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) {s ψ : ℝ} (spos : 0 < s)
    (sstep : s ≤ icosahedronEdge / q) (ssmall : s ≤ 1 / 2)
    (rsmall : (101 / 100 : ℝ) * s < Real.pi / 2) (ψpos : 0 < ψ) (ψsmall : ψ ≤ Real.pi)
    (bounds : ∀ (t : MeshFace q) (j k : Fin 3), j ≠ k →
      Real.tan ((101 / 100 : ℝ) * s) ≤ cornerGuardAltitude o hq t j k ∧
        ψ ≤ meshCornerAngle hq t j k) :
    VoronoiNetwork (fun a : meshSites q => (a : Space)) (meshEndpoint hq) s ψ := by
  refine
    { siteInjective := Subtype.val_injective
      siteUnit := meshSites_unit hq
      coversHemisphere := fun _ hu => exists_meshSite_inner_pos hq hu
      coversWalls := (voronoiWalls_eq_meshEdges qbig hq).le
      edgeUnit := meshEndpoint_unit hq
      edgePositive := meshEndpoint_angle_pos qbig hq
      edgeShort := fun e => (meshEndpoint_angle_lt_pi_div_two qbig hq e).le
      separated := fun _ _ different no_common x hx y hy =>
        meshArcs_separated_of_cornerGuardAltitude qbig hq o spos sstep rsmall
          (fun t j k ne => (bounds t j k ne).1) different no_common hx hy
      incident := ?_
      separationPositive := spos
      separationSmall := ssmall
      incidentPositive := ψpos
      incidentSmall := ψsmall }
  intro e f a b different common
  let t := incidentFace hq e a
  have e_mem : EdgeIncident e t := incidentFace_incident hq e a
  have e_normal : meshEndpoint hq e a = facetNormal hq t :=
    meshEndpoint_eq_facetNormal_incidentFace hq e a
  have f_normal : meshEndpoint hq f b = facetNormal hq t := common.symm.trans e_normal
  have f_face : incidentFace hq f b = t :=
    facetNormal_injective qbig hq
      ((meshEndpoint_eq_facetNormal_incidentFace hq f b).symm.trans f_normal)
  have f_mem : EdgeIncident f t := f_face ▸ incidentFace_incident hq f b
  obtain ⟨j, ej⟩ := exists_edgeOpposite_eq_of_incident hq t e e_mem
  obtain ⟨k, fk⟩ := exists_edgeOpposite_eq_of_incident hq t f f_mem
  have jk : j ≠ k := fun same => different (ej.symm.trans (same ▸ fk))
  have P : meshEndpoint hq e (!a) = facetNormal hq (adjacentFace hq t j) := by
    rw [← ej]
    exact meshEndpoint_other_eq_of_corner qbig hq t j a (ej.symm ▸ e_normal)
  have Q : meshEndpoint hq f (!b) = facetNormal hq (adjacentFace hq t k) := by
    rw [← fk]
    exact meshEndpoint_other_eq_of_corner qbig hq t k b (fk.symm ▸ f_normal)
  rw [e_normal, f_normal, P, Q]
  exact (bounds t j k jk).2

end Unfoldings.FewestNets.Icosahedron
